module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutExtGen
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutAmb

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.StandardType Matrix
open CFSG.Open (StatedSp)

variable {K : Type} [Field K]

theorem apply_eq_of_mem_torusAut_ycode_extension
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {φ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m}
    (hφ : φ ∈ torusAut ζ m (Ycode ζ m (.extension e))) :
    φ e = e ∧ ∀ l, e l = 0 → φ (Pi.single l 1) = Pi.single l 1 := by
  obtain ⟨y, hy, hconj⟩ := hφ
  have hyB := mem_blockGroup_extension_iff.mp (ycode_le_blockGroup ζ _ hy)
  refine ⟨tau_injective hζ m ?_, fun l hl => tau_injective hζ m ?_⟩
  · rw [← hconj, hyB.2, mul_inv_cancel_right]
  · have hu : ∀ i ∈ PlaneRaw.Code.extSupport e, (Pi.single l 1 : PlaneRaw.V m) i = 0 := by
      intro i hi
      refine Pi.single_eq_of_ne (fun h => (PlaneRaw.mem_extSupport e i).mp hi ?_) 1
      rw [h]
      exact hl
    rw [← hconj, ← commute_tau_of_mem_levi (ζ := ζ) hu hyB.1, mul_inv_cancel_right]

theorem torusAut_ycode_extension_subset (h : SpAmbientTorusAut) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {m : ℕ} (e : PlaneRaw.V m) :
    torusAut ζ m (Ycode ζ m (.extension e)) ⊆
      ((PlaneRaw.twistedPermGroupOn m e : Subgroup _) : Set _) := by
  intro φ hφ
  have hamb : φ ∈ torusAut ζ m ⊤ := torusAut_mono ζ m le_top hφ
  rw [h ζ m hK hζ] at hamb
  obtain ⟨he, hoff⟩ := apply_eq_of_mem_torusAut_ycode_extension hζ hφ
  exact PlaneRaw.mem_twistedPermGroupOn_of_mem_signedPermGroup hamb he hoff

theorem spExtTorusAut_of (h : SpAmbientTorusAut) : SpExtTorusAut := by
  intro K _ _ _ ζ m hK hζ e he
  exact Set.Subset.antisymm (torusAut_ycode_extension_subset h hK hζ e)
    (twistedPermGroupOn_subset_torusAut_ycode hK hζ he)

theorem spExtTorusAut_holds : SpExtTorusAut :=
  spExtTorusAut_of spAmbientTorusAut_holds

end CFSG.StandardType.GGQ2Frame.SpBlocks
