module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

namespace E6Nonsplit

section Label


theorem not_halfSplit_of_isComponentOf_top_of_quotient {C : Type} [Group C] [Finite C]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hQ : CFSG.IsQuasisimple C)
    (e : C ⧸ Subgroup.center C ≃* ↥(adjointGroup .E6 K)) {p : ℕ} (hp3 : p ≠ 3)
    (hq1 : ¬ p ∣ Nat.card K - 1) (h7 : ¬ (Nat.card K = 2 ∧ p = 7)) {X : Subgroup C}
    (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c := by
  have hXtop := ExcNonsplit.eq_top_of_isComponentOf_top hQ hX
  subst hXtop
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  set E : (↥(⊤ : Subgroup C) ⧸ Subgroup.center ↥(⊤ : Subgroup C)) ≃* ↥(adjointGroup .E6 K) :=
    (QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)).trans e
    with hE
  have hmod : MarkedModel (⟨.E6, 0, f⟩ : LargeEvenLabel)
      (↥(⊤ : Subgroup C) ⧸ Subgroup.center ↥(⊤ : Subgroup C)) :=
    (CFSG.ComponentClassification.CatLeafProof.lieModel_E6_of_mulEquiv hf1 hK E).2
  have hlab0 : LargeEvenInLambda2 (⟨.E6, 0, f⟩ : LargeEvenLabel) := ⟨hf1, rfl⟩
  have hGG : GGNbrNsE6Label p (⟨.E6, 0, f⟩ : LargeEvenLabel) :=
    ⟨rfl, by rw [← hK]; exact hq1, fun h => hp3 h.2, fun h => h7 ⟨by
      have h1 : (f : ℕ) = 1 := h.1
      rw [hK, h1]
      rfl, h.2⟩⟩
  exact NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab0 hGG hmod hlab hc hM c

theorem not_halfSplit_of_isComponentOf_top_ad {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp3 : p ≠ 3) (hq1 : ¬ p ∣ Nat.card K - 1) (h7 : ¬ (Nat.card K = 2 ∧ p = 7))
    {X : Subgroup ↥(adjointGroup .E6 K)} (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c :=
  not_halfSplit_of_isComponentOf_top_of_quotient
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
    (((QuotientGroup.quotientMulEquivOfEq
        (show Subgroup.center ↥(adjointGroup .E6 K) = ⊥ from center_adjointGroup_eq_bot)).trans
      QuotientGroup.quotientBot))
    hp3 hq1 h7 hX hlab hc hM

theorem not_halfSplit_of_isComponentOf_top_sc {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp3 : p ≠ 3) (hq1 : ¬ p ∣ Nat.card K - 1) (h7 : ¬ (Nat.card K = 2 ∧ p = 7))
    {X : Subgroup ↥(e6Data_valid.minGroup K)} (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c := by
  haveI : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  refine not_halfSplit_of_isComponentOf_top_of_quotient (K := K)
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) ?_ hp3 hq1 h7 hX hlab hc hM
  exact (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (e6Isogeny K) (e6Isogeny_surjective K))

end Label

end E6Nonsplit

end CFSG.StandardType
