--2/1/22

axioms P Q : Prop

#check P ∧ Q 
#check and P Q

axioms (p : P ) (q : Q)

example : P ∧ Q := and.intro p q

def func ( P Q : Prop ) (p : P) (q :Q) :  P ∧ Q := and.intro p q

def andElimLeft ( P Q : Prop ) (pq : P ∧ Q) : P := and.elim_left pq


theorem and_commutes  (P Q : Prop) (pq : P ∧ Q ) : Q ∧ P :=
and.intro (and.elim_right pq) (and.elim_left pq) 