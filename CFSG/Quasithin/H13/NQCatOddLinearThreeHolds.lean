module

public import CFSG.Quasithin.H13.NQCatOddLinearThreeInputs
public import CFSG.Quasithin.SteinbergBSQTEOddLinearThree

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F]

theorem preservingFixing_eq_steinberg (V₁ V₂ : Submodule F (Fin 3 → F)) :
    preservingFixing V₁ V₂ = SteinbergBS.QTEOddLinearThree.preservingFixing V₁ V₂ := by
  ext g
  constructor
  · intro hg
    have hinv : g⁻¹ ∈ preservingFixing V₁ V₂ := (preservingFixing V₁ V₂).inv_mem hg
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hi1, -⟩ := hinv
    refine ⟨fun v => ⟨fun hv => ?_, fun hv => hg1 v hv⟩, hg2⟩
    have h1 := hi1 _ hv
    change matrixAction F g⁻¹ (matrixAction F g v) ∈ V₁ at h1
    rwa [SteinbergBS.QTEOddLinearThree.matrixAction_apply_inv] at h1
  · rintro ⟨hg1, hg2⟩
    exact ⟨fun v hv => (hg1 v).mpr hv, hg2⟩

theorem oddLinearThreeInvolutionSylowStructure_holds [Finite F] :
    OddLinearThreeInvolutionSylowStructure F := by
  intro hF hq D _ hD
  have hD' : D ≤ CFSG.LinearGroups.scalarSubgroup 3 F :=
    hD.trans (Eq.trans (scalars_eq_center (n := 3) (K := F))
      CFSG.LinearGroups.scalarSubgroup_eq_center.symm).le
  obtain ⟨hSyl, hinv⟩ := SteinbergBS.odd_linear_three_involution_and_Sylow_structure hF hq D hD'
  refine ⟨hSyl, fun t ht => ?_⟩
  obtain ⟨z, ⟨hz, hzt⟩, huniq, hm, hp, hres, hinj, hiso, htmem, hcomm⟩ := hinv t ht
  rw [← preservingFixing_eq_steinberg] at hres hinj hiso htmem hcomm
  refine ⟨z, hz, hzt, huniq, hm, hp, hres, ?_, hiso, htmem, hcomm⟩
  intro a ha b hb hab
  exact congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)

end CFSG.Quasithin.H13.NQCat
