module

public import CFSG.LocalAnalysis.StandardType.GGE0PSUComp
public import CFSG.LocalAnalysis.StandardType.GGE0PSUPairing

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType.ClassicalPosition CFSG.LieType.SemisimpleCentralizers
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive
  unitaryInvolution_apply)

theorem ggE0At_PSU
    : GGE0At .PSU := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 g hg hEC C₀ hC₀
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hc : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn3 : 3 ≤ n := by omega
  have hker : ψ.ker ≤ Subgroup.center _ := hctx.2.2.2.2.1.2
  have hbG1 : b ∈ ggG1 ψ := ggBs_le_ggG1 hctx hb
  obtain ⟨s, hsJ, hs⟩ := exists_isGLLift_PSU hc n hn3 ψ hker hbG1.1 hbG1.2
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hc n
  have hτ := unitaryInvolution_involutive hc
  have hs'GU := conj_mem_heldGU_of_unitary hτ hP hsJ
  have hsp := hs.pow p
  rw [hctx.bstar.2.1.2 b hb] at hsp
  obtain ⟨a, ha⟩ := isGLLift_unique_PSU hc n ψ hker hsp isGLLift_one
  rw [inv_one, one_mul] at ha
  have hodd : Odd (orderOf (P * s * P⁻¹)) := by
    have h := orderOf_injective (MulAut.conj P).toMonoidHom (MulAut.conj P).injective s
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [h]
    exact odd_orderOf_of_pow_eq_scalar (hctx.prime.odd_of_ne_two hctx.ne_two) ha
  rw [← hctx.range_eq] at hC₀
  obtain ⟨J', hJ'q, hJ'C, rfl⟩ := ggE0Comp_PSU hc n ψ hker hP hs hC₀
  refine ggE0Concl_of_isGLLift_action _
    ((MulAut.conj P).injective.comp (Subgroup.subtype_injective _)) ψ hker hJ'q
    (ggE0Concl_centralizer_heldGU hτ (fun y => unitaryInvolution_apply _ 2 (f + 1) y) hc _
      hs'GU hodd hJ'C) (fun ε hε => ?_)
  have hεG1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSU hctx hg
    (hctx.d_le_bstar.trans (ggBs_le_ggG1 hctx)) hε
  obtain ⟨t, htJ, ht⟩ := exists_isGLLift_PSU hc n hn3 ψ hker hεG1.1 hεG1.2
  have hts : Commute t s := ggE0Pairing_PSU hctx s1 hg hEC hsJ hs ε hε t ht
  have hcomm : Commute (P * t * P⁻¹) (P * s * P⁻¹) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hts.map (MulAut.conj P).toMonoidHom
  refine ⟨(P * t * P⁻¹)⁻¹, Subgroup.inv_mem _ (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq,
      conj_mem_heldGU_of_unitary hτ hP htJ⟩), fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := ht u
  refine ⟨u', ?_, hu'ψ⟩
  show P * (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n).subtype u' *
      P⁻¹ = (P * t * P⁻¹)⁻¹⁻¹ *
        (P * (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n).subtype u *
          P⁻¹) * (P * t * P⁻¹)⁻¹
  rw [hu'j]
  group

end CFSG.StandardType
