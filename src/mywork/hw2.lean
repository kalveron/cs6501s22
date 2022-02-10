/-
The purpose of this assignment is to develop
and deepen your understanding of the concepts
we've covered so far: equality of values/terms 
of any type, and conjunction of propositions.
-/

/-
Compare and contrast the distinct ways that 
we represented these ideas in Lean.

- inductive eq  { α : Sort u }, α → α → Prop
- inductive and (α β : Prop) : Prop 

Each of "eq" and and builds "propositions", 
but they build them in different ways. 

For any given type, eq takes two *values* of
that type, yields a proposition "about" those
values, and provides constructors that define
the only possible proofs of a proposition of
this kind. 

By contrast, "and" takes two propositions, i.e., 
*types, not values*, as its arguments, reduces to
another proposition as a result, namely (and P Q), 
also written P ∧ Q, and also provide a constructor
(introduction axiom) for building proofs of this
type. 

Popping into the everyday language of programming
languages, we can say that "and" is a polymorphic
type; but, by contrast eq, defines a family of binary
(equality) relations *indexed by an arbitrary type*,
α. There's thus a separate binary equality relation
on terms for each distinct type, (α : Sort u).  
-/

/-
Ex 1: Embed the concept of the logical or (∨)
connective into Lean in the same style we used
to embed ∧. To do this we'll need to talk about
the introduction and elimination rules for or.
-/


namespace hidden

inductive or (α β : Prop) : Prop
| intro_left  (Q : Prop) (a : α) : or
| intro_right (P : Prop) (b : β) : or

#check or (3=3) (4=4)

theorem foo : or (3=3) (3=4) :=
or.intro_left  (3=4) rfl

example : or (3=4) (3=3) := 
or.intro_right (3=4) rfl



end hidden

#check @or

example : 3=3 ∨ 1=0 :=
or.intro_left (1=0) rfl

example : 1=0 ∨ 3=3 :=
or.intro_right (1=0) rfl

example : 3=3 ∨ 1=0 :=
or.inl rfl

example : 1=0 ∨ 3=3 :=
or.inr rfl

/-
#2. Let's using an inductive family to 
specify the successor relationship between
pairs of natural numbers. For any natural
numbers, n and m, (n, m) ∈ succ_rel if and
only if m = n + 1. Once you've done this,
state and prove the lemma, (0,1) ∈ succ_rel.
-/

#check and

--COmputational definition of the increment relation
--Ways to generate functions
example (n : ℕ) : ℕ := n + 1
example : ℕ → ℕ := λ ( n: ℕ ), n + 1

--Use this method to generate recursive functions
example : ℕ → ℕ
| n := n + 1

def incr (n : ℕ) : ℕ := n + 1 

--Declaritive specification of the increment relation
inductive succ_rel : ℕ → ℕ  → Prop
| intro (n m : ℕ) (h : m = n + 1) : succ_rel n m

#check succ_rel 3 4

#check succ_rel.intro

example : succ_rel 3 4 := succ_rel.intro 3 4 rfl 

-- example : succ_rel 3 5 := succ_rel.intro 3 5 rfl 

/-
theorem def_equivalent : ∀ (n m : ℕ), (m = incr n) ↔ succ_rel n m :=
begin
  intros,
  split,
  assume h, 
  apply succ_rel.intro,
  
end


-/

theorem def_equivalent : ∀ (n m : ℕ), (m = incr n) ↔ succ_rel n m :=
begin
  intros,
  apply iff.intro _ _,

  --Forward
  assume h, 
  rw h,
  unfold incr,
  apply succ_rel.intro,
  trivial,

 --Backward
  assume h,
  cases h,
  unfold incr,
  apply h_h
  
end
