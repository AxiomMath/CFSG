module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaDefs
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3Mathieu
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint
open CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree (coverGen)
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
  (coverGen_M22_of_cert coverGen_eq_top_of_equiv)

theorem r891GammaM22_holds : R891GammaM22 := by
  intro X _ _ ⟨ψ⟩ E hE hE9
  have hM22 : Nat.card ↥NativeSporadic.M22 = 443520 := by
    obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
    exact le_antisymm
      ((Nat.card_le_card_of_surjective _ CFSG.Sporadic.Bridge.M22.toNative_surjective).trans
        hle)
      CFSG.Sporadic.Bridge.M22.le_card_native
  have hcard : ¬ 3 ^ 3 ∣ Nat.card ↥NativeSporadic.M22 := by
    rw [hM22]
    norm_num
  let ψ₁ : NativeSporadic.Carrier .M22 ≃* ↥NativeSporadic.M22 := MulEquiv.refl _
  let φ : X ≃* ↥NativeSporadic.M22 := ψ.trans ψ₁
  have hcov : coverGen E = ⊤ := by
    refine coverGen_eq_top_of_equiv φ ?_
    exact coverGen_M22_of_cert hcard _
      (by rw [Subgroup.card_map_of_injective φ.injective, hE9])
  rw [eq_top_iff]
  calc (⊤ : Subgroup X) = coverGen E := hcov.symm
    _ ≤ rankThreeGamma 1 3 E := by
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | ⟨hxa, -⟩)
      · exact CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma
          hE ha ha1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      · exact CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma
          hE ha ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hxa)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
