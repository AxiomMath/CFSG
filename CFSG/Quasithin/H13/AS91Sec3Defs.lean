module

public import CFSG.Milestones.ASVolI.H13

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

@[expose] def octsOf (S : Finset (Finset (Fin 24))) : Finset (Finset (Fin 24)) :=
  ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => p.1 ∪ p.2

@[expose] def TrioIn (l S : Finset (Finset (Fin 24))) : Prop := l ⊆ octsOf S

@[expose] def Coplanar (l k : Finset (Finset (Fin 24))) : Prop :=
  ∃ S, IsSextet S ∧ TrioIn l S ∧ TrioIn k S

@[expose] def InZeta (l : Finset (Finset (Fin 24))) (O : Finset (Fin 24)) : Prop :=
  O ∈ l ∨ ∃ u ∈ l, Disjoint O u

instance (l : Finset (Finset (Fin 24))) : DecidablePred (InZeta l) := fun O => by
  unfold InZeta
  infer_instance

@[expose] def Delta (l k : Finset (Finset (Fin 24))) : Fin 5 → Prop
  | 0 => k = l
  | 1 => k ≠ l ∧ ¬ Disjoint k l
  | 2 => Disjoint k l ∧ Coplanar l k
  | 3 => (k.filter (InZeta l)).card = 1
  | 4 => (k.filter (InZeta l)).card = 0

@[expose] def Xi (U W : Finset (Finset (Fin 24))) : Fin 4 → Prop
  | 0 => W = U
  | 1 => (octsOf W ∩ octsOf U).card = 3
  | 2 => (octsOf W ∩ octsOf U).card = 1
  | 3 => Disjoint (octsOf W) (octsOf U)

@[expose] def Kappa (U l : Finset (Finset (Fin 24))) : Fin 4 → Prop
  | 0 => TrioIn l U
  | 1 => (l ∩ octsOf U).card = 1
  | 2 => Disjoint l (octsOf U) ∧ ∃ W, IsSextet W ∧ Xi U W 1 ∧ TrioIn l W
  | 3 => Disjoint l (octsOf U) ∧ ¬ ∃ W, IsSextet W ∧ Xi U W 1 ∧ TrioIn l W

@[expose] def IsDiscOrOval (U : Finset (Finset (Fin 24)))
    (D : Finset (Finset (Finset (Fin 24)))) : Prop :=
  (∃ d, IsTrio d ∧ TrioIn d U ∧
      ∀ k, k ∈ D ↔ IsTrio k ∧ TrioIn k U ∧ k ≠ d ∧ ¬ Disjoint k d) ∨
    (D.card = 5 ∧ ∀ k ∈ D, IsTrio k ∧ TrioIn k U ∧ ∀ k' ∈ D, k ≠ k' → Disjoint k k')

end CFSG.Quasithin.H13.AS91.M24G
