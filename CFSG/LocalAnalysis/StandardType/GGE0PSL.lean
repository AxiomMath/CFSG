module

public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
public import CFSG.LocalAnalysis.StandardType.GGE0PSLPairing

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType.ClassicalPosition

theorem ggE0At_PSL
    : GGE0At .PSL := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 g hg hEC C₀ hC₀
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hker : ψ.ker ≤ Subgroup.center _ := hctx.2.2.2.2.1.2
  have hbG1 : b ∈ ggG1 ψ := ggBs_le_ggG1 hctx hb
  obtain ⟨s, hs⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ hker hbG1.1 hbG1.2
  have hsp := hs.pow p
  rw [hctx.bstar.2.1.2 b hb] at hsp
  obtain ⟨a, ha⟩ := isGLLift_unique_PSL m (GaloisField 2 f) ψ hker hsp isGLLift_one
  rw [inv_one, one_mul] at ha
  have hodd : Odd (orderOf s) :=
    odd_orderOf_of_pow_eq_scalar (hctx.prime.odd_of_ne_two hctx.ne_two) ha
  rw [← hctx.range_eq] at hC₀
  obtain ⟨J', hJ'q, hJ'C, rfl⟩ := ggE0Comp_PSL m ψ hker hs hC₀
  refine ggE0Concl_of_isGLLift_action Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective ψ hker hJ'q
    (ggE0Concl_centralizer_generalLinear s hodd hJ'C) (fun ε hε => ?_)
  have hεG1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSL hctx hg
    (hctx.d_le_bstar.trans (ggBs_le_ggG1 hctx)) hε
  obtain ⟨t, ht⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ hker hεG1.1 hεG1.2
  have hts : Commute t s := ggE0Pairing_PSL hctx s1 hg hEC hs ε hε t ht
  refine ⟨t⁻¹, Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr hts.eq),
    fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := ht u
  exact ⟨u', by rw [hu'j, inv_inv], hu'ψ⟩

end CFSG.StandardType
