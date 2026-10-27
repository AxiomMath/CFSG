module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item224Res5Proof

@[expose] def oddFixed (X : Type*) [Group X] (T : Subgroup (MulAut X)) : Subgroup X :=
  Subgroup.closure {x | (∀ t ∈ T, t x = x) ∧ Odd (orderOf x)}

@[expose] def AutElliptic (X : Type*) [Group X] (T : Subgroup (MulAut X)) : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
    (oddFixed X T).map MulAut.conj ≤ Subgroup.normalizer (P : Set (MulAut X)) →
      (∀ p ∈ P, ∀ x ∈ oddFixed X T, p x = x) ∧ IsCyclic P

@[expose] def InnerThreeFixed (X : Type*) [Group X] (E : Subgroup (MulAut X)) : Prop :=
  ∀ x : X, orderOf x = 3 → (∀ e ∈ E, e x = x) → MulAut.conj x ∈ E

@[expose] def AutEllipticTorus (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
    InnerThreeFixed X E →
    (∃ x : X, orderOf x = 3 ∧ x ∉ Subgroup.center X ∧ ∀ e ∈ E, e x = x) →
    ∀ T : Subgroup (MulAut X), IsPGroup 2 T → T ≠ ⊥ →
      T ≤ Subgroup.centralizer (E : Set (MulAut X)) → AutElliptic X T

end Item224Res5Proof

open Item224Res5Proof

@[expose] def KS224Sp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    Nonempty (X ≃* projSp 2 (GaloisField 2 n)) → AutEllipticTorus X

@[expose] def KS224U4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 0 < n → Even n →
    Nonempty (X ≃* projSU 4 2 n) → AutEllipticTorus X

@[expose] def KS224U5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 5 2 2) → AutEllipticTorus X

end CFSG.RankThree.PartTwo.Sec21
