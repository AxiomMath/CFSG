module

import CFSG.RankThree.PartTwo.Sec15.Item155Proof
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_char_normal_of_hyp322TwoJ (h322 : Item3_22TwoJ) {H R : Subgroup G}
    (hyp : Hyp322 H R) (hQR : CFSG.Open.pCoreOf 2 H ≤ R) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
      H ≤ Subgroup.normalizer (C : Set G) := by
  obtain ⟨hRH, hF, hJ2, hE4, hCe⟩ := hyp
  set R₀ := R.subgroupOf H with hR₀
  have hle : CFSG.pCore 2 ↥H ≤ R₀ := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQR ((mem_pCoreOf_iff155 x).mpr hx))
  have e₀ : ↥R₀ ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
  have hR₀2 : IsPGroup 2 ↥R₀ := hR2.of_equiv e₀.symm
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  have : Nontrivial ↥R₀ := e₀.symm.injective.nontrivial
  have key : ∀ D : Subgroup ↥R₀, D.Characteristic → D ≠ ⊥ → (D.map R₀.subtype).Normal →
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G) := by
    intro D hDc hD1 hDn
    refine ⟨(D.map R₀.subtype).map H.subtype, ?_, ?_, ?_, le_normalizer_map_of_normal155 hDn⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective,
        Subgroup.map_eq_bot_iff_of_injective _ R₀.subtype_injective]
      exact hD1
    · rintro _ ⟨y, ⟨z, -, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp z.2
    · refine characteristic_subgroupOf_map hRH (Subgroup.map_subtype_le D) ?_
      have hsub : (D.map R₀.subtype).subgroupOf R₀ = D :=
        Subgroup.comap_map_eq_self_of_injective R₀.subtype_injective D
      have hDc' := hDc
      rw [← hsub] at hDc'
      exact hDc'
  by_cases hz : (CFSG.omegaOneCenter (⊤ : Subgroup ↥R₀)).map R₀.subtype ≤ Subgroup.center ↥H
  · exact key _ (omegaOneCenter_top_characteristic155 _) (omegaOneCenter_top_ne_bot hR₀2)
      (Subgroup.normal_of_le_center hz)
  · exact key _ (higherElemThompson_characteristic155 _ 0) (higherElemThompson_zero_ne_bot hR₀2)
      (h322 ↥H hF hJ2 R₀ hle hE4 hCe hz)

end CFSG.RankThree.PartTwo.Sec15
