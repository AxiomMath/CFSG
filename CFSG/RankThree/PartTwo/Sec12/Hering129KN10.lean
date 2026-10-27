module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec12.Item12Res3ProofM12

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem conj_eq_of_comm_inv {G : Type} [Group G] [Finite G] {c a t : G} {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 c) (haK : a ∈ K) (hta : t * a = a * t)
    (htc : t * c * t⁻¹ = c⁻¹) (ha : a ∉ Sec4.thetaQuotCentralizer K) :
    t ∈ Subgroup.normalizer (K : Set G) := by
  set K' := K.map (MulAut.conj t).toMonoidHom
  have hK' : K' ∈ thetaComponentsAt 3 c := by
    have h1 := KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hK t
    rwa [htc, Res3Proof.thetaComponentsAt_inv'] at h1
  have haK' : a ∈ K' := by
    refine ⟨a, haK, ?_⟩
    change t * a * t⁻¹ = a
    rw [hta, mul_inv_cancel_right]
  by_contra htN
  have hne : K' ≠ K := fun h => htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  exact ha (mem_thetaQuotCentralizer_of_ne hK' hK hne haK' (Subgroup.le_normalizer haK))

theorem mem_normalizer_of_commute_core {G : Type} [Group G] [Finite G] {A Y : Subgroup G}
    {c x m : G} (hcA : c ∈ A) (hcY : c ∈ Y) (hY : Core129 A c x Y)
    (hcx : c ∉ Subgroup.zpowers x) (hmx : m * x = x * m) (hmc : m * c = c * m) :
    m ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYx, hAN, hAC, -⟩ := hY
  set Y' := Y.map (MulAut.conj m).toMonoidHom
  have hY' : Y' ∈ thetaComponentsAt 3 x := by
    have h1 := KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hYx m
    rwa [hmx, mul_inv_cancel_right] at h1
  have hcY' : c ∈ Y' := by
    refine ⟨c, hcY, ?_⟩
    change m * c * m⁻¹ = c
    rw [hmc, mul_inv_cancel_right]
  by_contra hmN
  have hne : Y' ≠ Y := fun h => hmN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hc := mem_thetaQuotCentralizer_of_ne hY' hYx hne hcY' (hAN hcA)
  apply hcx
  rw [← hAC]
  exact ⟨hcA, hc⟩

end CFSG.RankThree.PartTwo.Sec12
