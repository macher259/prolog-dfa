% DFA internal representation: tuple consisting of:
% Q - all states in the automaton,
% Tree - BST tree made from Delta,
% Delta - transition function,
% I - initial state,
% F - final states,
% Alphabet - alphabet of the language.

% correct(+Automaton, -Representation)
% True if Automaton is a correct representation of 
% a deterministic finite automaton.
correct(dfa(Delta, I, F), dfa(Q, Tree, Delta, I, F, Alphabet)) :- 
    buildTreeFromDelta(Delta, Tree), % Build BST, because "speed".
    checkWhetherFinalStatesContainDuplicates(Delta),
    getStates(dfa(Delta, I, F), _QFromDelta, Q), % Get all states.
    getAlphabet(Delta, Alphabet),
    checkTotality(Delta, Alphabet, Q).

% Checks whether transition function Delta is total.
% Also chether alphabet is not empty. 
checkTotality(Delta, Alphabet, Q) :-
    getOutEdges(Delta, OutEdges),
    sort(OutEdges, UniqueOutEdges),
    length(UniqueOutEdges, UniqueOutEdgesLength),
    length(Delta, UniqueOutEdgesLength),
    length(Alphabet, AL),
    AL > 0,
    length(Q, QL),
    UniqueOutEdgesLength is AL * QL.

getOutEdges([], []).
getOutEdges([fp(A, B, _) | Fs], [pair(A, B) | Ps]) :-
    getOutEdges(Fs, Ps).

checkWhetherFinalStatesContainDuplicates(F) :-
    sort(F, SortedF),
    length(F, L), length(SortedF, L).

getStates(dfa(Delta, I, F), BareQ, Q) :-
    getStatesFromDelta(Delta, DuplicatedQ),
    sort(DuplicatedQ, BareQ),
    append(BareQ, F, NearlyQ),
    sort([I | NearlyQ], Q). % Remove duplicates.

getAlphabet(Delta, Alphabet) :-
    guessAlphabet(Delta, DuplicatedAlphabet),
    sort(DuplicatedAlphabet, Alphabet). % Remove duplicates.

buildTreeFromDelta(S, T) :- buildTreeFromDelta(S, nil, T).
buildTreeFromDelta([], A, A).
buildTreeFromDelta([X | S], A, T) :-
    insertBST(A, X, AT),
    buildTreeFromDelta(S, AT, T).

insertBST(nil, X, node(nil, X, nil)).
insertBST(node(L, fp(A, B, C), R), fp(D, E, F), node(NL, fp(A, B, C), R)) :-
    A @>= D, !,
    insertBST(L, fp(D, E, F), NL).
insertBST(node(L, fp(A, B, C), R), fp(D, E, F), node(L, fp(A, B, C), NR)) :-
    A @< D,
    insertBST(R, fp(D, E, F), NR).

findBST(node(_L, fp(A, B, C), _R), fp(A, B, C)).
findBST(node(L, fp(A, _B, _C), _R), fp(D, E, F)) :-
    A @>= D,
    findBST(L, fp(D, E, F)).
findBST(node(_L, fp(A, _B, _C), R), fp(D, E, F)) :-
    A @< D,
    findBST(R, fp(D, E, F)).

getStatesFromDelta([], []).
getStatesFromDelta([fp(X, _, Y) | Fs], [Y | [X | States]]) :-
    getStatesFromDelta(Fs, States).

guessAlphabet([], []).
guessAlphabet([fp(_, C, _) | Fs], [C | Cs]) :- guessAlphabet(Fs, Cs).

%==============================================================================
% empty(+Automaton).
% True if Automaton's language is empty.
empty(dfa(Delta, [], I)) :-
    correct(dfa(Delta, [], I), _).
empty(A) :-
    correct(A, dfa(_Q, Tree, _Delta, I, F, _Alphabet)),
    notOneReachable(F, Tree, I, R), !, 
    length(R, L), length(F, L).

% Checks that every final state is reachable the from initial state.
notOneReachable([], _Tree, _I, []).
notOneReachable([F | Fs], Tree, I, [_R | Rs]) :-
    \+ go(I, F, Tree),
    notOneReachable(Fs, Tree, I, Rs).
notOneReachable([F | Fs], Tree, I, Rs) :-
    go(I, F, Tree),
    notOneReachable(Fs, Tree, I, Rs).

% Simple DFS.
go(Start, Goal, Tree) :-
	go(Start, Goal, [], Tree).
go(Goal, Goal, _Visited, _Tree).	
go(State, Goal, Visited, Tree) :-
	connected(State, Next, Tree),
    \+ member(Next, Visited),
    go(Next, Goal, [Next | Visited], Tree).
	
connected(A, B, Tree) :-
    findBST(Tree, fp(A, _, B)).

%==============================================================================
% accept(+Automaton, ?Word).
% True if Automaton accepts Word.
accept(A, W) :-
    correct(A, dfa(_Q, Tree, _Delta, I, F, _Alphabet)),
    F \= [],
    length(W, L),
    walk(I, F, W, Tree, L).

% DFS-like graph traversal for word of length L
walk(Start, F, Word, Tree, L) :-
    nonvar(Word),
	walk(Start, _Q, F, Word, Tree, L).
walk(Start, F, Word, Tree, L) :-
    var(Word), walk(Start, _Q, F, Word, Tree, L+1).
walk(State, _Q, F, [], _Tree, 0) :-
    member(State, F).
walk(State, Q, F, [C | W], Tree, L) :-
    connectedBy(State, Next, C, Tree),
    L2 is L - 1,
    walk(Next, Q, F, W, Tree, L2).

connectedBy(A, B, C, Tree) :-
    findBST(Tree, fp(A, C, B)).

%==============================================================================
% subsetEq(+Automaton1, +Automaton2)
% True if Automaton1 is a subset of Automaton2.
subsetEq(Automaton1, Automaton2) :-
    correct(Automaton1, dfa(_Q1, Tree1, _Delta1, I1, F1, Alphabet1)),
    correct(Automaton2, dfa(_Q2, Tree2, _Delta2, I2, F2, Alphabet2)),
    Alphabet1 == Alphabet2,
    checkIfIntersectionEmpty(I1, I2, F1, F2, Tree1, Tree2), !.

checkIfIntersectionEmpty(State1, State2, Goal1, Goal2, Tree1, Tree2) :-
    \+ goDouble(State1, State2, Goal1, Goal2,
         [pair(State1, State2)], Tree1, Tree2).

% DFS on both graphs at the same time.
goDouble(State1, State2, Goal1, Goal2, _Visited, _T1, _T2) :-
    member(State1, Goal1),
    \+ member(State2, Goal2), !.
goDouble(State1, State2, Goal1, Goal2, Visited, Tree1, Tree2) :-
    bothConnected(State1, State2, Next1, Next2, Tree1, Tree2),
    \+ member(pair(Next1, Next2), Visited),
    goDouble(Next1, Next2, Goal1, Goal2, 
        [pair(Next1, Next2) | Visited], Tree1, Tree2).

bothConnected(State1, State2, Next1, Next2, Tree1, Tree2) :-
    findBST(Tree1, fp(State1, C, Next1)),
    findBST(Tree2, fp(State2, C, Next2)).

%==============================================================================
% equal(+Automaton1, +Automaton2).
% Checks whether two automata are equal.
equal(Automaton1, Automaton2) :-
    subsetEq(Automaton1, Automaton2),
    subsetEq(Automaton2, Automaton1).

