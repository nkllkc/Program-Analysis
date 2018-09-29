package util;

import java.util.*;

/**
 * Class represents rooted directed graph.
 * @param <T> type of information stored within a node.
 */
public class DirectedGraph<T> {
    protected Map<T, Set<Pair<T, String>>> predecessors = new HashMap<>();
    protected Map<T, Set<Pair<T, String>>> successors = new HashMap<>();

    protected T entryNode = null;

    public DirectedGraph() {}

    public Map<T, Set<Pair<T, String>>> getPredecessors() {
        return predecessors;
    }

    public Map<T, Set<Pair<T, String>>> getSuccessors() {
        return successors;
    }

    public T getEntryNode() {
        return entryNode;
    }

    /**
     * Adding an edge to the graph.
     *
     * WARNING: Self edge is possible.
     *
     * @param nodeFrom node from.
     * @param nodeTo node to.
     * @param label if {@code null}. it means there is no label.
     */
    public void addEdge(T nodeFrom, T nodeTo, String label) {
        if (entryNode == null) {
            entryNode = nodeFrom;
        }

        addNode(nodeFrom);
        addNode(nodeTo);

        successors.get(nodeFrom).add(new Pair<>(nodeTo, label));
        predecessors.get(nodeTo).add(new Pair<>(nodeFrom, label));
    }

    public void addNode(T node) {
        if (node != null && !predecessors.containsKey(node)) {
            predecessors.put(node, new HashSet<>());
        }
        if (node != null && !successors.containsKey(node)) {
            successors.put(node, new HashSet<>());
        }
    }

    /**
     * Creates reversed graph based on a given input graph.
     *
     * @param inputGraph input graph.
     * @return reversed {@code DirectedGraph}.
     */
    public DirectedGraph<T> getReversedGraph(DirectedGraph<T> inputGraph) {
        DirectedGraph<T> reversed = new DirectedGraph<>();
        for (T from : inputGraph.successors.keySet()) {
            reversed.addNode(from);
            for (Pair<T, String> pairTo : inputGraph.successors.get(from)) {
                reversed.addEdge(pairTo.getFirst() /* to */, from, pairTo.getSecond() /* label */);
            }
        }
        return reversed;
    }

    /**
     * Topological ordering of the directed graph.
     *
     * @return {@code List} of nodes of generic type T in topological order.
     */
    public List<T> topologicalSort() {
        Stack<T> stack = new Stack<>();

        Set<T> visited = new HashSet<>();

        for (T node : predecessors.keySet()) {
            if (visited.contains(node)) {
                continue;
            }

            topologicalSortUtil(node, visited, stack);
        }

        List<T> result = new LinkedList<>();

        while (!stack.empty()) {
            result.add(stack.pop());
        }

        return result;
    }

    private void topologicalSortUtil(T node, Set<T> visited, Stack<T> stack) {
        visited.add(node);
        for (Pair<T, String> successor : successors.get(node)) {
            if (visited.contains(successor.getFirst() /* node */ )) {
                continue;
            }
            topologicalSortUtil(successor.getFirst(), visited, stack);
        }
        stack.push(node);
    }

}
