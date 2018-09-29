import com.sun.istack.internal.NotNull;
import soot.*;
import soot.jimple.ConditionExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.*;
import soot.options.Options;
import soot.toolkits.graph.pdg.EnhancedUnitGraph;
import util.DirectedGraph;
import util.Pair;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

/**
 * Control Flow Graph implementation.
 */
public class CFG extends DirectedGraph<String> {
    private static final String LINE_NUMBER_TAG = "LineNumberTag";
    private static final String DOTTY_HEADER = "digraph control_flow_graph {\n"
            + "node [shape = rectangle]; entry exit;\n" + "node [shape = circle];\n";
    private static final String DOTTY_FOOTER = "\n}";

    private SootClass sootClass;
    private SootMethod sootMethod;
    private Body body;

    private Map<String, Set<String>> definedVariables = new HashMap<>();
    private Map<String, Set<String>> usesDefined = new HashMap<>();

    private Set<String> allLocals = new HashSet<>();

    /**
     * Constructor.
     * <b>Warning: Does not construct a CFG, method constructCFG needs to be run.</b>
     * <p>
     * Todo: Add IllegalArgumentException if method with methodName is not available.
     *
     * @param classDirectory directory where the class binaries are.
     * @param className      name of the class which method will be used for construction of CFG.
     * @param methodName     name of the method over which CFG will be constructed.
     */
    public CFG(String classDirectory, String className, String methodName) {
        String sootClassPath = Scene.v().getSootClassPath() + File.pathSeparator + classDirectory;
        Scene.v().setSootClassPath(sootClassPath);

        Options.v().set_keep_line_number(true);
        Options.v().setPhaseOption("jb", "use-original-names");

        sootClass = Scene.v().loadClassAndSupport(className);
        Scene.v().loadNecessaryClasses();
        sootClass.setApplicationClass();

        sootMethod = sootClass.getMethodByName(methodName);
        if (sootMethod == null) {
            throw new IllegalArgumentException("No method named " + methodName + " within a class " + className);
        }
        body = sootMethod.retrieveActiveBody();

        construct();
    }

    private void construct() {
        Unit[] arrayOfUnits = body.getUnits().toArray(new Unit[body.getUnits().size()]);

        Set<Integer> returnStmts = new HashSet<>();

        Integer firstLine = null;

        EnhancedUnitGraph graph = new EnhancedUnitGraph(body);

        for (int i = 0; i < arrayOfUnits.length; i++) {
            Unit unit = arrayOfUnits[i];

            // If a line has no line number attached, it's skipped.
            if (!unit.hasTag(LINE_NUMBER_TAG)) {
                continue;
            }


            int lineNum = Integer.parseInt(unit.getTag(LINE_NUMBER_TAG).toString());

            if (unit instanceof JAssignStmt) {
                List<ValueBox> boxes = unit.getUseBoxes();
                if (boxes != null && boxes.size() == 3) {
                    ValueBox first = boxes.get(0);
                    if (first instanceof RValueBox) {
                        if (i - 4 > 0) {
                            if (arrayOfUnits[i - 1] instanceof JIfStmt) {
                                if (arrayOfUnits[i - 2] instanceof JAssignStmt) {
                                    List<ValueBox> test = arrayOfUnits[i - 2].getDefBoxes();
                                    if (test != null && test.size() > 0) {
                                        if (test.get(0).getValue().toString()
                                                .equals(boxes.get(2).getValue().toString())) {
                                            arrayOfUnits[i] = arrayOfUnits[i - 1];
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if (firstLine == null) {
                firstLine = lineNum;
                addEdge("entry", firstLine.toString(), null);
            }

            if (unit instanceof JIfStmt) {
                JIfStmt ifStmt = (JIfStmt) unit;
                Stmt target = ifStmt.getTarget();
                int targetLine = Integer.parseInt(target.getTag(LINE_NUMBER_TAG).toString());

                for (Unit pred : graph.getPredsOf(unit)) {
                    System.out.println(pred.getJavaSourceStartLineNumber() + ": " + pred);
                }

                for (Unit succ : graph.getSuccsOf(unit)) {
                    System.out.println(succ.getJavaSourceStartLineNumber() + ": " + succ);
                }
                System.out.println("\n");
                addEdge(Integer.toString(lineNum),
                        Integer.toString(targetLine),
                        ((ConditionExpr) ifStmt.getCondition()).getSymbol().trim());
            } else if (unit instanceof JGotoStmt) {
                JGotoStmt gotoStmt = (JGotoStmt) unit;
                int targetLine = Integer.parseInt(gotoStmt.getTarget().getTag(LINE_NUMBER_TAG).toString());
                addEdge(Integer.toString(lineNum), Integer.toString(targetLine), null);
            } else if (unit instanceof JLookupSwitchStmt) {
                JLookupSwitchStmt switchStmt = (JLookupSwitchStmt) unit;
                boolean isStringSwitch = false;
                if (i > 0 && arrayOfUnits[i - 1] instanceof JAssignStmt) {
                    JAssignStmt assignStmt = (JAssignStmt) arrayOfUnits[i - 1];
                    if (assignStmt.containsInvokeExpr()
                            && "hashCode".equals(assignStmt.getInvokeExpr().getMethod().getName())) {
                        String[] labels = new String[switchStmt.getTargetCount()];
                        if (switchStmt.getDefaultTarget() instanceof JTableSwitchStmt) {
                            JTableSwitchStmt defaultTarget = (JTableSwitchStmt) switchStmt.getDefaultTarget();
                            for (int j = 0; j < switchStmt.getTargetCount(); j++) {
                                Unit target = switchStmt.getTargets().get(j);
                                if (!(target instanceof JAssignStmt)) {
                                    break;
                                }
                                JAssignStmt assignStmtTarget = (JAssignStmt) target;
                                if (assignStmtTarget.getInvokeExpr() == null
                                        || assignStmtTarget.getInvokeExpr().getMethod() == null
                                        || !"equals".equals(assignStmtTarget.getInvokeExpr().getMethod().getName())) {
                                    break;
                                }
                                String label = assignStmtTarget.getInvokeExpr().getArgs().get(0).toString();
                                labels[j] = label.substring(1, label.length() - 1);
                            }
                            for (int j = defaultTarget.getLowIndex(); j <= defaultTarget.getHighIndex(); j++) {
                                Unit stringSwitchTarget = defaultTarget.getTargets()
                                        .get(j - defaultTarget.getLowIndex());
                                int branchDest = Integer
                                        .parseInt(stringSwitchTarget.getTag(LINE_NUMBER_TAG).toString());
                                addEdge(
                                        Integer.toString(lineNum),
                                        Integer.toString(branchDest),
                                        labels[j - defaultTarget.getLowIndex()]);
                            }
                            Unit defaultUnit = defaultTarget.getDefaultTarget();
                            int branchDest = Integer.parseInt(defaultUnit.getTag(LINE_NUMBER_TAG).toString());
                            addEdge(Integer.toString(lineNum), Integer.toString(branchDest), "default");
                            while (arrayOfUnits[i] != defaultTarget) {
                                i++;
                            }
                            isStringSwitch = true;
                        }
                    }
                }

                if (isStringSwitch) {
                    continue;
                }

                Unit defaultTarget = switchStmt.getDefaultTarget();

                for (int j = 0; j < switchStmt.getTargetCount(); j++) {
                    Unit target = switchStmt.getTargets().get(j);
                    String label = switchStmt.getLookupValues().get(j).toString();
                    if (target == null || target == defaultTarget) {
                        continue;
                    }
                    int branchDest = Integer.parseInt(target.getTag(LINE_NUMBER_TAG).toString());

                    addEdge(Integer.toString(lineNum), Integer.toString(branchDest), label);
                }

                int branchDest = Integer.parseInt(defaultTarget.getTag(LINE_NUMBER_TAG).toString());
                addEdge(Integer.toString(lineNum),
                        Integer.toString(branchDest),
                        defaultTarget != null && defaultTarget != unit ? "default" : null);
                if (!definedVariables.containsKey(Integer.toString(lineNum))) {
                    definedVariables.put(Integer.toString(lineNum), new HashSet<>());
                }
            } else if (unit instanceof JTableSwitchStmt) {
                JTableSwitchStmt switchStmt = (JTableSwitchStmt) unit;

                boolean fl = false;
                if (i > 0 && arrayOfUnits[i - 1] instanceof JAssignStmt) {
                    JAssignStmt assignStmt = (JAssignStmt) arrayOfUnits[i - 1];
                    if (assignStmt.containsInvokeExpr()
                            && "hashCode".equals(assignStmt.getInvokeExpr().getMethod().getName())) {

                        if (switchStmt.getDefaultTarget() instanceof JTableSwitchStmt) {
                            JTableSwitchStmt tableSwitchStmt = (JTableSwitchStmt) switchStmt.getDefaultTarget();
                            Unit defaultTarget = tableSwitchStmt.getDefaultTarget();
                            List<Unit> realTargets = new ArrayList<>();
                            for (Unit target : tableSwitchStmt.getTargets()) {
                                if (defaultTarget == target) {
                                    continue;
                                }
                                realTargets.add(target);
                            }

                            int k = 0;
                            for (int j = switchStmt.getLowIndex(); j <= switchStmt.getHighIndex(); j++) {
                                Unit target = switchStmt.getTargets().get(j - switchStmt.getLowIndex());
                                if (target == tableSwitchStmt) {
                                    continue;
                                }
                                JAssignStmt assignStmtTarget = (JAssignStmt) target;

                                if (assignStmtTarget.getInvokeExpr() == null
                                        || assignStmtTarget.getInvokeExpr().getMethod() == null
                                        || !"equals".equals(assignStmtTarget.getInvokeExpr().getMethod().getName())) {
                                    fl = true;
                                    break;
                                }
                                int branchDest = Integer
                                        .parseInt(realTargets.get(k++).getTag(LINE_NUMBER_TAG).toString());
                                String label = assignStmtTarget.getInvokeExpr().getArgs().get(0).toString();
                                label = label.substring(1, label.length() - 1);
                                addEdge(Integer.toString(lineNum), Integer.toString(branchDest), label);
                            }

                            int branchDest = Integer
                                    .parseInt(defaultTarget.getTag(LINE_NUMBER_TAG).toString());
                            addEdge(Integer.toString(lineNum), Integer.toString(branchDest), "default");


                            fl = true;
                            while (arrayOfUnits[i] != tableSwitchStmt) {
                                i++;
                            }
                        }
                    }
                }

                if (fl) {
                    if (!definedVariables.containsKey(Integer.toString(lineNum))) {
                        definedVariables.put(Integer.toString(lineNum), new HashSet<>());
                    }
                    continue;
                }

                Unit defaultTarget = switchStmt.getDefaultTarget();
                for (int j = switchStmt.getLowIndex(); j <= switchStmt.getHighIndex(); j++) {
                    Unit target = switchStmt.getTargets().get(j - switchStmt.getLowIndex());
                    if (target == null || target == defaultTarget) {
                        continue;
                    }
                    int branchDest = Integer.parseInt(target.getTag(LINE_NUMBER_TAG).toString());
                    addEdge(Integer.toString(lineNum), Integer.toString(branchDest), Integer.toString(j));
                }

                int branchDest = Integer.parseInt(defaultTarget.getTag(LINE_NUMBER_TAG).toString());
                addEdge(Integer.toString(lineNum),
                        Integer.toString(branchDest),
                        defaultTarget != null && defaultTarget != unit ? "default" : null);
            } else if (unit instanceof JReturnStmt || unit instanceof JReturnVoidStmt) {
                returnStmts.add(lineNum);
            }


            Unit previousUnit = arrayOfUnits[i - 1];
            if (previousUnit.fallsThrough() && previousUnit.hasTag(LINE_NUMBER_TAG)) {
                int lineFrom = Integer.parseInt(previousUnit.getTag(LINE_NUMBER_TAG).toString());
                String label = null;
                if (arrayOfUnits[i - 1] instanceof JIfStmt) {
                    label = "!" + ((ConditionExpr) ((JIfStmt) previousUnit).getCondition()).getSymbol().trim();
                }
                addEdge(Integer.toString(lineFrom), Integer.toString(lineNum), label);
            }

            if (unit instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) unit;
                String variableName = assignStmt.getDefBoxes().get(0).getValue().toString();
                if (!variableName.contains("$")) {
                    if (variableName.contains("#")) {
                        variableName = variableName.substring(0, variableName.indexOf('#'));
                    }
                    if (!definedVariables.containsKey(Integer.toString(lineNum))) {
                        definedVariables.put(Integer.toString(lineNum), new HashSet<>());
                    }
                    definedVariables.get(Integer.toString(lineNum)).add(variableName);
                }
            }
        }


        for (int i : returnStmts) {
            addEdge(Integer.toString(i), "exit", null);
        }


        if (firstLine == null) {
            addEdge("entry", "exit", null);
        }

        if (body.getParameterLocals() != null && body.getParameterLocals().size() > 0) {
            for (Local param : body.getParameterLocals()) {
                if (!definedVariables.containsKey(entryNode)) {
                    definedVariables.put(entryNode, new HashSet<>());
                }
                definedVariables.get(entryNode).add(param.getName());
            }
        }

        for (String node : predecessors.keySet()) {
            allLocals.addAll(definedVariables.get(node));
        }

        for (Unit unit : arrayOfUnits) {

            // If a line has no line number attached, it's skipped.
            if (!unit.hasTag(LINE_NUMBER_TAG)) {
                continue;
            }

            int lineNum = Integer.parseInt(unit.getTag(LINE_NUMBER_TAG).toString());

            System.out.println(lineNum + ": " + unit + ", falls through: " + unit.fallsThrough());

            for (ValueBox box : unit.getUseBoxes()) {
                String label = box.getValue().toString();
                System.out.println("\t\t" + box + ": " + label);
                if (label.contains("]")) {
                    label = label.substring(0, label.indexOf("["));
                    label.trim();
                }
                if (!allLocals.contains(label)) {
                    continue;
                }

                if (!usesDefined.containsKey(Integer.toString(lineNum))) {
                    usesDefined.put(Integer.toString(lineNum), new HashSet<>());
                }
                usesDefined.get(Integer.toString(lineNum)).add(label);
            }
        }

    }

    private static void writeEdge(BufferedWriter writer, String from, String to, String label) throws IOException {
        writer.write("\t" + from + " -> " + to);
        if (label != null) {
            writer.write(" [label = \"" + label + "\"]");
        }
        writer.write(";\n");
    }

    public void writeToDotty(String fileName) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(fileName));
        writer.write(DOTTY_HEADER);
        for (String from : successors.keySet()) {
            for (Pair<String, String> toPair : successors.get(from)) {
                writeEdge(writer, from, toPair.getFirst() /* node */, toPair.getSecond() /* label */);
            }
        }
        writer.write(DOTTY_FOOTER);
        writer.close();
    }

    public static void main(@NotNull String[] args) {
        if (args.length != 3) {
            System.err.println("Wrong number of elements.");
            return;
        }

        CFG controlFlowGraph =
                new CFG(args[2] /* classDirectory */, args[0] /* className */, "main");

        try {
            controlFlowGraph.writeToDotty(args[1]);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
