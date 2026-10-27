module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Conv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

@[expose] def K4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .ONan →
    ∀ H : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ H →
      ∀ σ ∈ H, orderOf σ = 3 →
        Nat.card ↥(H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) ∣ 6480 ∧
        inSubgroup (aschbacherSolvableCore 3)
          (H ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) = ⊥

@[expose] def K9J2Order : Prop :=
  ∀ y : CFSG.Blueprint.NativeSporadic.J2, orderOf y ≠ 21

@[expose] def K9J2Out : Prop :=
  ∀ σ : MulAut CFSG.Blueprint.NativeSporadic.J2, σ ^ 7 = 1 →
    σ ∈ (MulAut.conj : CFSG.Blueprint.NativeSporadic.J2 →* MulAut _).range

@[expose] def K9Five : Prop :=
  ¬ 5 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 3 1) ∧
    ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
      ¬ 5 ∣ Nat.card X

@[expose] def K9G2Rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f →
    CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 f →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

theorem k9G2Rank_holds :
    K9G2Rank := fun X _ _ f _ h =>
  CFSG.LocalAnalysis.AGL81TheoremCD.Section7.Conv76.four_le_pRank_of_g2_three h

@[expose] def K2ONanCentralizer : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) Y →
    ∀ x : Y, orderOf x = 3 → x ∉ Subgroup.center Y →
      let C : Subgroup Y := Subgroup.centralizer ({x} : Set Y)
      let J : Subgroup Y := ⁅C, C⁆
      Nat.card C = 3240 ∧ Subgroup.center Y ≤ J ∧ Nat.card J = 1080 ∧
        C = Subgroup.zpowers x ⊔ J ∧
        IsAlt (J ⧸ (Subgroup.center Y).subgroupOf J) 6

@[expose] def K6ONanClasses : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) Y →
    ∀ x y : Y, orderOf x = 3 → x ∉ Subgroup.center Y →
      orderOf y = 3 → y ∉ Subgroup.center Y → ∃ g : Y, g * x * g⁻¹ = y

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
