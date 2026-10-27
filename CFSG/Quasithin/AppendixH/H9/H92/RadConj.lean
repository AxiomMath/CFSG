module

public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.Quasithin.AppendixH.H9.H92.RadTransfer.RadV1Conjugation

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem exists_conj_radV1 (U D : Subgroup (PairN 5)) (hU : U ≤ V1n 5) (hD : D ≤ V1n 5)
    (hUr : rk ↥U = 3) (hDr : rk ↥D = 2 ∨ rk ↥D = 3) :
    ∃ g ∈ Mg 5, conjAut g (RadV1 5 D) = RadV1 5 U := by
  have hU3 : Module.finrank (ZMod 2) (v1Space 5 U) = 3 :=
    (finrank_v1Space_eq_rk U hU).trans hUr
  have hD' := finrank_v1Space_eq_rk D hD
  rcases hDr with hD2 | hD3
  · have hdp : Module.finrank (ZMod 2) (dotPerp 5 (v1Space 5 D)) = 3 := by
      have := finrank_dotPerp_add 5 (v1Space 5 D)
      omega
    obtain ⟨B, hB⟩ := exists_gl_map_submodule_eq
      (D₁ := dotPerp 5 (v1Space 5 D)) (D₂ := v1Space 5 U) (hdp.trans hU3.symm)
    refine ⟨pairActN 5 B * swapN 5, outer_mem_Mg B, ?_⟩
    exact (conjAut_mul (pairActN 5 B) (swapN 5) (RadV1 5 D)).trans
      ((congrArg (conjAut (pairActN 5 B)) (conjAut_swapN_map_radMat (v1Space 5 D))).trans
        (conjAut_pairActN_map_radMat B hB))
  · have hD3' : Module.finrank (ZMod 2) (v1Space 5 D) = 3 := hD'.trans hD3
    obtain ⟨B, hB⟩ := exists_gl_map_submodule_eq
      (D₁ := v1Space 5 D) (D₂ := v1Space 5 U) (hD3'.trans hU3.symm)
    exact ⟨pairActN 5 B, Lg_le_Mg (pairActN_mem_Lg B), conjAut_pairActN_map_radMat B hB⟩

end CFSG.ASVolI.ChH
