module

public import CFSG.Certificates.SchreierChainData
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.Certificates.Kernel.PkEnum

open CFSG.Certificates CFSG.KS.PK

@[expose] def wd (n : Nat) : Nat := n.log2 + 1

theorem lt_two_pow_wd (n : Nat) : n < 2 ^ wd n := Nat.lt_log2_self

@[expose] def PkOK (n : Nat) (p : Nat × Nat) : Prop :=
  ∀ i < n, fd (wd n) p.1 i < n ∧ fd (wd n) p.2 i < n ∧ fd (wd n) p.2 (fd (wd n) p.1 i) = i ∧
    fd (wd n) p.1 (fd (wd n) p.2 i) = i

abbrev VP (n : Nat) := {p : Nat × Nat // PkOK n p}

@[expose] def pk (n : Nat) (f : Nat → Nat) : Nat := enc (wd n) f n

theorem fd_pk {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < n) {i : Nat} (hi : i < n) :
    fd (wd n) (pk n f) i = f i :=
  fd_enc (fun j hj => (hf j hj).trans (lt_two_pow_wd n)) hi

theorem mulV_ok {n : Nat} (a b : VP n) :
    PkOK n (pk n fun i => fd (wd n) a.1.1 (fd (wd n) b.1.1 i),
      pk n fun i => fd (wd n) b.1.2 (fd (wd n) a.1.2 i)) := by
  have h1 : ∀ j < n, fd (wd n) a.1.1 (fd (wd n) b.1.1 j) < n :=
    fun j hj => (a.2 _ (b.2 j hj).1).1
  have h2 : ∀ j < n, fd (wd n) b.1.2 (fd (wd n) a.1.2 j) < n :=
    fun j hj => (b.2 _ (a.2 j hj).2.1).2.1
  intro i hi
  refine ⟨by rw [fd_pk h1 hi]; exact h1 i hi, by rw [fd_pk h2 hi]; exact h2 i hi, ?_, ?_⟩
  · rw [fd_pk h1 hi, fd_pk h2 (h1 i hi), (a.2 _ (b.2 i hi).1).2.2.1, (b.2 i hi).2.2.1]
  · rw [fd_pk h2 hi, fd_pk h1 (h2 i hi), (b.2 _ (a.2 i hi).2.1).2.2.2, (a.2 i hi).2.2.2]

@[expose] def mulV {n : Nat} (a b : VP n) : VP n :=
  ⟨(pk n fun i => fd (wd n) a.1.1 (fd (wd n) b.1.1 i),
    pk n fun i => fd (wd n) b.1.2 (fd (wd n) a.1.2 i)), mulV_ok a b⟩

theorem oneV_ok (n : Nat) : PkOK n (pk n fun i => i, pk n fun i => i) := by
  have h : ∀ j < n, j < n := fun j hj => hj
  intro i hi
  rw [fd_pk h hi, fd_pk h hi]
  exact ⟨hi, hi, rfl, rfl⟩

@[expose] def oneV (n : Nat) : VP n := ⟨(pk n fun i => i, pk n fun i => i), oneV_ok n⟩

@[expose] def invV {n : Nat} (a : VP n) : VP n :=
  ⟨(a.1.2, a.1.1), fun i hi => ⟨(a.2 i hi).2.1, (a.2 i hi).1, (a.2 i hi).2.2.2, (a.2 i hi).2.2.1⟩⟩

@[expose] def pkp {n : Nat} (a : VP n) : Equiv.Perm (Fin n) where
  toFun i := ⟨fd (wd n) a.1.1 i, (a.2 i i.2).1⟩
  invFun i := ⟨fd (wd n) a.1.2 i, (a.2 i i.2).2.1⟩
  left_inv i := Fin.ext (a.2 i i.2).2.2.1
  right_inv i := Fin.ext (a.2 i i.2).2.2.2

theorem codeV_ok {n : Nat} (σ : Equiv.Perm (Fin n)) :
    PkOK n (pk n fun i => if h : i < n then (σ ⟨i, h⟩ : Nat) else 0,
      pk n fun i => if h : i < n then (σ⁻¹ ⟨i, h⟩ : Nat) else 0) := by
  have h1 : ∀ j < n, (if h : j < n then (σ ⟨j, h⟩ : Nat) else 0) < n := by
    intro j hj
    rw [dif_pos hj]
    exact (σ _).2
  have h2 : ∀ j < n, (if h : j < n then (σ⁻¹ ⟨j, h⟩ : Nat) else 0) < n := by
    intro j hj
    rw [dif_pos hj]
    exact (σ⁻¹ _).2
  intro i hi
  refine ⟨by rw [fd_pk h1 hi]; exact h1 i hi, by rw [fd_pk h2 hi]; exact h2 i hi, ?_, ?_⟩
  · rw [fd_pk h1 hi, fd_pk h2 (h1 i hi), dif_pos hi, dif_pos (σ _).2]
    simp
  · rw [fd_pk h2 hi, fd_pk h1 (h2 i hi), dif_pos hi, dif_pos (σ⁻¹ _).2]
    simp

@[expose] def codeV {n : Nat} (σ : Equiv.Perm (Fin n)) : VP n :=
  ⟨(pk n fun i => if h : i < n then (σ ⟨i, h⟩ : Nat) else 0,
    pk n fun i => if h : i < n then (σ⁻¹ ⟨i, h⟩ : Nat) else 0), codeV_ok σ⟩

structure StV (n : Nat) where
  entries : List (Fin n × VP n)
  queue : List (Fin n)

@[expose] def discoverV {n : Nat} (q : StV n) (y : Fin n) (t : VP n) : StV n :=
  if (q.entries.lookup y).isSome then q else ⟨q.entries ++ [(y, t)], q.queue ++ [y]⟩

@[expose] def stepV {n : Nat} (steps : List (VP n)) (q : StV n) : StV n :=
  match q.queue with
  | [] => q
  | x :: pending =>
    let tx := (q.entries.lookup x).getD (oneV n)
    steps.foldl (fun st s => discoverV st (pkp s x) (mulV s tx)) ⟨q.entries, pending⟩

@[expose] def runV {n : Nat} (steps : List (VP n)) : Nat → StV n → StV n
  | 0, q => q
  | fuel + 1, q => runV steps fuel (stepV steps q)

@[expose] def stepsV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) (i : Nat) :
    List (VP n) :=
  let g := Sc.filter fun s => (base.toList.take i).all fun b => decide (pkp s b = b)
  g ++ g.map invV

@[expose] def levelV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) (i : Fin k) :
    StV n :=
  runV (stepsV Sc base i.val) n ⟨[(base.get i, oneV n)], [base.get i]⟩

@[expose] def transV {n : Nat} (q : StV n) : List (VP n) :=
  (q.entries.map Prod.fst).map fun x => (q.entries.lookup x).getD (oneV n)

@[expose] def productsV {n : Nat} : List (List (VP n)) → List (VP n)
  | [] => [oneV n]
  | T :: Ts => T.flatMap fun t => (productsV Ts).map (mulV t)

@[expose] def enumV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) : List (VP n) :=
  productsV ((List.finRange k).map fun i => transV (levelV Sc base i))

@[expose] def siftResV {n : Nat} : List (Fin n × StV n) → VP n → Option (VP n)
  | [], h => some h
  | (b, q) :: levels, h =>
    match q.entries.lookup (pkp h b) with
    | none => none
    | some t => siftResV levels (mulV (invV t) h)

@[expose] def siftV {n : Nat} (levels : List (Fin n × StV n)) (h : VP n) : Bool :=
  match siftResV levels h with
  | none => false
  | some r => schreierPermEq (pkp r) 1

@[expose] def levelsV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) (i : Nat) :
    List (Fin n × StV n) :=
  ((List.finRange k).drop i).map fun j => (base.get j, levelV Sc base j)

@[expose] def schV {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) : Bool :=
  ((Sc.filter fun s => base.toList.all fun b => decide (pkp s b = b)).all fun s =>
    schreierPermEq (pkp s) 1) &&
  (List.finRange k).all fun i =>
    let q := levelV Sc base i
    q.entries.all fun e => (stepsV Sc base i.val).all fun s =>
      match q.entries.lookup (pkp s e.1) with
      | none => false
      | some ty => siftV (levelsV Sc base (i.val + 1)) (mulV (mulV (invV ty) s) e.2)

@[expose] def strongV {n : Nat} (Q : RawSchreierDatum n) : List (VP n) :=
  Q.strong.toList.map codeV

@[expose] def elemsV {n : Nat} (Q : RawSchreierDatum n) : List (Equiv.Perm (Fin n)) :=
  (enumV (strongV Q) Q.base).map pkp

@[expose] def siftP {n : Nat} (Q : RawSchreierDatum n) (σ : Equiv.Perm (Fin n)) (i : Nat) : Bool :=
  siftV (levelsV (strongV Q) Q.base i) (codeV σ)

@[expose] def orderV {n : Nat} (Q : RawSchreierDatum n) : Nat :=
  ((List.finRange Q.baseCount).map fun i => (levelV (strongV Q) Q.base i).entries.length).prod

@[expose] def schP {n : Nat} (Q : RawSchreierDatum n) : Bool := schV (strongV Q) Q.base

end CFSG.Certificates.Kernel.PkEnum

end
