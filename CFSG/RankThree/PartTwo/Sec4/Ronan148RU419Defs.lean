module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

structure CfgU419 (X : Type) [Group X] (α : MulAut X) (Y : Subgroup X) (m : ℕ) : Prop where
  pow_three : α ^ 3 = 1
  ne_one : α ≠ 1
  le_autFix : Y ≤ autFix α
  isSubnormal : (Y.subgroupOf (autFix α)).IsSubnormal
  isPerfect : Group.IsPerfect Y
  odd : Odd m
  one_lt : 1 < m
  cover : ∃ π : Y →* projSU 3 2 m, Function.Surjective π ∧ Nat.Coprime (Nat.card π.ker) 3

section Kinds


@[expose] def ConclU419 (X : Type) [Group X] (α : MulAut X) (m : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * m) K) (e : X ≃* unitaryPSU h 3),
      (stdPinnedPSU3 h).HasKind (MulAut.congr e α) .field) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 3 ∧
      ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ m) ∧
        ∃ e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          trialityHasKind σ (MulAut.congr e α) .graphField)

@[expose] def RowU419 (X : Type) [Group X] : Prop :=
  ∀ (α : MulAut X) (Y : Subgroup X) (m : ℕ), CfgU419 X α Y m → ConclU419 X α m

@[expose] def NoCfgU419 (X : Type) [Group X] : Prop :=
  ∀ (α : MulAut X) (Y : Subgroup X) (m : ℕ), ¬ CfgU419 X α Y m

theorem NoCfgU419.rowU419 {X : Type} [Group X] (h : NoCfgU419 X) : RowU419 X :=
  fun α Y m hc => absurd hc (h α Y m)

@[expose] def RowsU419One : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46One X → RowU419 X

@[expose] def RowsU419Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Two X → RowU419 X

@[expose] def RowsU419Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Three X → RowU419 X

@[expose] def RowsU419Four : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Four X → RowU419 X

@[expose] def RowsU419Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Five X → RowU419 X

@[expose] def RowsU419Six : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Six X → RowU419 X

@[expose] def RowsU419Seven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Seven X → RowU419 X

@[expose] def RowsU419Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsList46Eight X → RowU419 X

end Kinds

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
