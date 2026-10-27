module

public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4Comorphism
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open WithConv CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain in
theorem antiSp_lang_aut (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (b : ℕ) :
    ∃ S₀ : MulAut (antiSp L),
      (∀ g : antiSp L,
        glMat (S₀ g : GL (Fin 4) L) = (minorMap (glMat g)).map (fun x => x ^ 2 ^ b)) ∧
      ∀ x : antiSp L, ∃ h : antiSp L, x = h⁻¹ * S₀ h := by
  obtain ⟨D⟩ := nonempty_spPointData L
  refine ⟨suzukiAut L b, fun g => glMat_suzukiAut L b g, fun x => ?_⟩
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity (sigmaHom D b)
    (m := 2) (by norm_num) (sigmaAlg_tangent D b) (D.e.symm x)
  refine ⟨D.e h, ?_⟩
  have h1 := congrArg D.e hh
  rw [MulEquiv.apply_symm_apply, map_mul, map_inv, e_pointMap_sigmaHom] at h1
  exact h1

end CFSG.RankThree.PartOne.KE
