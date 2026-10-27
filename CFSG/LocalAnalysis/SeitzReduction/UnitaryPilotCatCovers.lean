module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree centerFixedProjection
  orderOf_centerQuotientAut centerQuotientAut_mem_range odd_card_center_of_twoFree
  twoFree_centerQuotientAut)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall isComponent_map_centerFixedProjection
  odd_card_center_of_twoSmall_inner twoSmall_centerQuotientAut)

theorem card_center_dvd_of_surjective {D D' : Type} [Group D] [Group D'] [Finite D]
    (φ : D →* D') (hφ : Function.Surjective φ) (e : D ⧸ center D ≃* D' ⧸ center D') :
    Nat.card (center D') ∣ Nat.card (center D) := by
  have hdvd := Subgroup.card_dvd_of_surjective (f := φ) hφ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center D),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center D'), ← Nat.card_congr e.toEquiv]
    at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd

theorem odd_card_center_map_centerFixedProjection {K : Type} [Group K] [Finite K] {τ : MulAut K}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D) (hZD : Odd (Nat.card (center D))) :
    Odd (Nat.card (center (D.map (centerFixedProjection τ)))) := by
  obtain ⟨-, ⟨e⟩⟩ := isComponent_map_centerFixedProjection hD
  exact hZD.of_dvd_nat (card_center_dvd_of_surjective _
    ((centerFixedProjection τ).subgroupMap_surjective D) e)

theorem catSUmCovers : CatSUmCovers := by
  intro K _ _ hK τ hτ m f D hD hDm
  have : Group.IsPerfect K := hK.1
  obtain ⟨hD', ⟨e⟩⟩ := isComponent_map_centerFixedProjection hD
  refine ⟨orderOf_centerQuotientAut hτ, centerQuotientAut_mem_range,
    D.map (centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hDm,
    odd_card_center_map_centerFixedProjection hD,
    fun hodd => ⟨odd_card_center_of_twoFree hτ hodd, twoFree_centerQuotientAut hD hτ hodd⟩,
    fun hin hsmall => ?_⟩
  have hZ := odd_card_center_of_twoSmall_inner hτ hin hsmall
  exact ⟨hZ, twoSmall_centerQuotientAut hD hZ hsmall⟩

end CFSG.SeitzReduction.UnitaryPilot
