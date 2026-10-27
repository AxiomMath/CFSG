module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  localRank)

@[expose] def CoverSLThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    Subgroup.center X ≠ ⊥ → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      IsoLThreePi (X ⧸ Subgroup.center X) p e → IsSLThreeEpsAt X (p ^ e)

@[expose] def CoverSLThree46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    Subgroup.center X ≠ ⊥ → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e → (p = 2 ∨ e ≤ 2) →
      IsoLThreePi (X ⧸ Subgroup.center X) p e → IsSLThreeEpsAt X (p ^ e)

theorem CoverSLThree.toCoverSLThree46 (h : CoverSLThree) : CoverSLThree46 :=
  fun X _ _ hq hZ3 hZ p e _ he _ hpi => h X hq hZ3 hZ p e he hpi

@[expose] def CoverCenterThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    (Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)) ∨
      Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) →
    Nat.card (Subgroup.center X) ∣ 3

@[expose] def CoverU43Center : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) → Nat.card (Subgroup.center X) ∣ 9

@[expose] def NineCoverU43RankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 9 →
    Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) → 4 ≤ localRank 3 X

structure CoverInputs46 : Prop where
  slThree : CoverSLThree46
  centerThree : CoverCenterThree
  u43 : CoverU43Center
  u43Rank : NineCoverU43RankFour

structure BridgeExceptional46 : Prop where
  g2Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
    Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 2 q.exponent
  trialityD4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group .trialityD4 2
      q.exponent
  reeF4 : ∀ (m : ℕ) (hm : (LieTypeIndex.reeF4 m).Valid),
    Blueprint.ReeTitsModel (CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group .twistedF4 2 (2 * m + 1)
  tits : ∀ ht : LieTypeIndex.tits.Valid,
    Blueprint.ReeTitsModel (CFSGIndex.lie ⟨.tits, ht⟩).Group .Tits 2 1

@[expose] def sporadics42not46 : List SporadicName := [.Ly, .Suz, .ONan, .Co3, .Co2, .HN, .Th]

structure RankThree46 : Prop where
  ree27 : ∀ hr : (LieTypeIndex.reeG2 1).Valid,
    ∀ [Finite (CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group],
      3 ≤ localRank 3 (CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  sporadic : ∀ s ∈ sporadics42not46, ∀ [Finite (CFSGIndex.sporadic s).Group],
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group
  omega8PlusTwo : ∀ [Finite (projOmegaPlus 4 (GaloisField 2 1))],
    3 ≤ localRank 3 (projOmegaPlus 4 (GaloisField 2 1))
  omega8MinusTwo : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    ∀ [Finite (projOmegaMinus 3 (GaloisField 2 1) b c)],
      3 ≤ localRank 3 (projOmegaMinus 3 (GaloisField 2 1) b c)
  f4Two : ∀ [Finite (CFSGIndex.lie f4TwoIndex).Group],
    3 ≤ localRank 3 (CFSGIndex.lie f4TwoIndex).Group

structure Inputs46 : Prop where
  cover : CoverInputs46
  bridge : BridgeExceptional46
  rank : RankThree46

end CFSG.RankThree.PartTwo.Sec4.Census
