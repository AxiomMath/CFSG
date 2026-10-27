module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedM11)

@[expose] def OddCenterFree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ K : Subgroup X, IsQuasisimple K →
      IsPGroup 3 (Subgroup.center K) → Subgroup.center K = ⊥

@[expose] def OddTwoRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ K : Subgroup X, CFSG.Assembly.twoRank K ≤ 2

@[expose] def OddThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P ≤ 9

@[expose] def OddFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ x g : X, x ^ 5 = 1 → x ≠ 1 → g * x * g⁻¹ = x ^ 2 → p = 5

@[expose] def OddU34Excl : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ K : Subgroup X, StatedClassicalModel K .PSU 3 2 2 → False

@[expose] def OddL3U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → e ≤ 2 →
    Sec4.IsoLThreePi X p e → ∀ K : Subgroup X, IsSimpleGroup K →
    ∀ r f : ℕ, r.Prime → r ≠ 2 → 1 ≤ f →
      (StatedClassicalModel K .PSL 3 r f ∨ StatedClassicalModel K .PSU 3 r f) →
      Ronan148K.L3SigType X K

@[expose] def OddL2Excl : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r f : ℕ), r.Prime → r ≠ 2 → 1 ≤ f → IsSimpleGroup S →
    StatedClassicalModel S .PSL 2 r f →
    (∀ P : Subgroup S, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P ≤ 9) →
    ∀ E : Subgroup (MulAut S), Nat.card E = 9 → (∀ ε ∈ E, ε ^ 3 = 1) →
      (⊤ : Subgroup S) ≤ (⨆ (ε : MulAut S) (_ : ε ∈ E) (_ : ε ≠ 1),
        pPrimeCoreOf 3 (Sec4.autFix ε)) → False

@[expose] def InspectSig148L3LocEven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), 1 ≤ e →
    (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; Sec4.IsoLThreePi X 2 e) → Sec4.IsList46 X →
    ∀ E : Subgroup (MulAut X), Nat.card E = 9 → (∀ ε ∈ E, ε ^ 3 = 1) → LocE X E →
      IsPGroup 3 (fixE E) →
      ∀ K : Subgroup X, (∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) → Group.IsPerfect K → K ≠ ⊥ →
        IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
        Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) →
        K ≤ (⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1),
          pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) →
        Ronan148K.L3SigType X K

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
