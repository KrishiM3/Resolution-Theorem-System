/* Dual Clause Form Program
Propositional operators are: neg, and, or, imp, revimp, uparrow, downarrow, notimp and notrevimp. 
*/

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* member(Item, List) :- Item occurs in List. */ 

member(X, [X | _]).

member(X, [_ | Tail]) :- 
    member(X, Tail).

/* remove(Item, List, Newlist) :- Newlist is the result of removing all occurences of Item from List. */

remove(X, [], []).

remove(X, [X | Tail], Newtail) :-
    remove(X, Tail, Newtail).

remove(X, [Head | Tail], [Head | Newtail]) :-
    remove(X, Tail, Newtail).

/* combines two lists together */
combine([], List, List). % Base case: When first list is empty, result is second list
combine([X|Xs], Ys, [X|Zs]) :-
    combine(Xs, Ys, Zs). % Recursively combine the tail of the first list with the second list

/* conjuctive(X) :- X is an alpha formula. */

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(_ equiv _).
conjunctive(neg(_ notequiv _)).

/* disjunctive(X) :- X is a beta formula. */

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).
disjunctive(_ notequiv _). 
disjunctive(neg(_ equiv _)).

/* unary(X) :- X is a double negation, or a negated constant. */

unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z) :- Y and Z are the components of the formula X, as defined in the alpha and beta tables. */

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y). 
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

/* Add the decomposition of equiv and not equiv */
components(X equiv Y, (X imp Y) , (Y imp X)).
components(neg (X equiv Y) , neg(X imp Y) , neg(Y imp X)).
components(X notequiv Y, neg(X imp Y) , neg(Y imp X)).
components(neg(X notequiv Y), (X imp Y), (Y imp X)).
/* component(X, Y) :- Y is the component of the unary formula X. */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion process to Old, which is a generalized disjunction of generalized conjunctions. */


singlestep([Conjunction | Rest], New) :-
    member(Formula, Conjunction),
    unary(Formula), 
    component(Formula, Newformula),
    remove(Formula, Conjunction, Temporary),
    Newconjunction = [Newformula | Temporary],
    sort(Newconjunction,NoDupe), /* remove duplicates */
    New = [NoDupe | Rest].

singlestep([Conjunction | Rest], New) :-
    member(Alpha, Conjunction),
    conjunctive(Alpha) ,
    components(Alpha, Alphaone, Alphatwo),
    remove(Alpha, Conjunction, Temporary),
    Newconone = [Alphaone | Temporary],
    sort(Newconone, NoDupeOne),
    Newcontwo = [Alphatwo | Temporary],
    sort(Newcontwo, NoDupeTwo),
    New = [NoDupeOne, NoDupeTwo | Rest].

singlestep([Conjunction | Rest], New) :-
    member(Beta, Conjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo), 
    remove(Beta, Conjunction, Temporary),
    Newcon = [Betaone, Betatwo | Temporary],
    sort(Newcon,NoDupe),
    New = [NoDupe | Rest].

singlestep([Conjunction | Rest], [Conjunction | Newrest]) :-
    singlestep(Rest, Newrest).

/* expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old. */

expand(Dis, Newdis) :-
    singlestep(Dis, Temp),
    expand(Temp, Newdis).

expand(Dis, Dis).


/* clauseform(X, Y) :- Y is the clause form of X. */

clauseform(X, Y) :- expand([[X]], Y).

/* closed(Tableau) :- every branch of Tableau contains a contradiction. */

closed(Resolution) :- member([], Resolution).

/* Resolve,
    performs resolution rule once on the clauses,
    takes in the list of remaining clauses, 
    clauses that have already been expanded and are no longer necessary, 
    returns the new set of clauses and updated list of redundant clauses.
*/

resolutionstep([Head | Tail],DupeList,NewDupeList, NewCNF) :-
% identify if there is a valid clause to resolve with the head
    append([Head],Tail,ActualList),
    not(last(ActualList,Head)),
    member(P, Head),
    member(Clause, Tail),
    member(Q, Clause),
    negation(P, Q),
    /* now combine after removing */
    remove(P, Head, NewHead),
    remove(Q, Clause, NewClause),
    combine(NewHead, NewClause, Resolvant),
    sort(Resolvant, SortedResolvant),
    %check if the resolvant is either in the dupelist or the list of current clauses
    not(member(SortedResolvant,ActualList)),
    not(member(SortedResolvant,DupeList)),
    NewCNF = [SortedResolvant | ActualList],
    NewDupeList = DupeList.

%this resolve is called when the head of the clause list cannot resolve on anything, thus we add it to the redundant list
resolutionstep([Head | Tail],DupeList,NewDupeList, NewCNF) :-
    append([Head],Tail,ActualList),
    not(last(ActualList,Head)),
    append(DupeList,[Head],Temp),
    NewDupeList = Temp,
    NewCNF = Tail.
    
%both resolves only work if it is non empty, if there is no two elements to resolve on then we are done



negation(P,Q) :- P = neg Q.
negation(P,Q) :- neg P = Q.




test(X) :-
    if_then_else(expand_and_close(neg X), yes, no).

yes :-
    write(yes).

no :-
    write(no).

/* if_then_else(P, Q, R) :- either P and Q, or not P and not R. */

if_then_else(P, Q, R) :- 
    P,
    !,
    Q.

if_then_else(P, Q, R) :-
    R.

/* expand_and_close(Tableau) :- some expansion of Tableau closes. */
    
expand_and_close(Tableau) :-
    closed(Tableau).

expand_and_close(Tableau) :-
    clauseform(Tableau, CNF),
    !,
    resolution(CNF,[] ,NewList, NewCNF),
    closed(NewCNF).


%calls the resolution stops it when there are no longer any changes to the CNF or a empty list is found.

resolution(List,Any,NewAny,Newlist) :-
    closed(List).

resolution(List,Any,NewAny, Newlist) :-
    resolutionstep(List,Any,NewAny, AlteredList),
    sort(AlteredList, Temp),
    !,
    resolution(Temp,NewAny,EvenNewerAny, Newlist).


