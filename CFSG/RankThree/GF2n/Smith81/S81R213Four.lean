module

public import CFSG.RankThree.GF2n.Smith81.S81R213Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section Four

variable [Finite G] {M Q Z B : Subgroup G}

private theorem conj_pow_inv {x u : G} (hxu : x * u * x⁻¹ = u⁻¹) (n : ℕ) :
    x * u ^ n * x⁻¹ = (u ^ n)⁻¹ := by
  rw [← conj_pow, hxu, inv_pow]

private theorem pow_mul_inv_of_inv {x u : G} (hxx : x * x = 1) (hxu : x * u * x⁻¹ = u⁻¹) (n : ℕ) :
    u ^ n * x = x * (u ^ n)⁻¹ := by
  have h := conj_pow_inv hxu n
  have hA : x * u ^ n = (u ^ n)⁻¹ * x := mul_inv_eq_iff_eq_mul.mp h
  calc u ^ n * x = (x * x) * u ^ n * x := by rw [hxx, one_mul]
    _ = x * (x * u ^ n) * x := by group
    _ = x * ((u ^ n)⁻¹ * x) * x := by rw [hA]
    _ = x * (u ^ n)⁻¹ * (x * x) := by group
    _ = x * (u ^ n)⁻¹ := by rw [hxx, mul_one]

theorem pow_four_eq_one (hNF : Smith212ENonfusedE3LStatement) (IH : Smith1981Below (Nat.card G))
    (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    {x y : G} (hxc : IsConj z x) (hyc : IsConj z y)
    (hv : (x * y) ^ 4 = 1 ∨ InZClass Z ((x * y) ^ 4)) : (x * y) ^ 4 = 1 := by
  rcases hv with hv | hvz
  · exact hv
  have H : StrothHyp M Q Z := hSE.toCfg.ctx.hyp
  by_contra hv1
  have hvc : IsConj z ((x * y) ^ 4) := isConj_of_inZClass H hz hz1 hvz
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H hz hyc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨u, hu⟩ : ∃ u, u = x * y := ⟨_, rfl⟩
  rw [← hu] at hv1 hvc
  have hvv : u ^ 4 * u ^ 4 = 1 := mul_self_eq_one_of_isConj_Z H hz hvc
  have hvinv : (u ^ 4)⁻¹ = u ^ 4 := inv_eq_of_mul_eq_one_right hvv
  have hxu : x * u * x⁻¹ = u⁻¹ := by
    rw [hu, hxinv, mul_inv_rev, hyinv, hxinv]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hxx, one_mul]
  have hyu : y * u * y⁻¹ = u⁻¹ := by
    rw [hu, hyinv, mul_inv_rev, hyinv, hxinv]
    calc y * (x * y) * y = y * x * (y * y) := by group
      _ = y * x := by rw [hyy, mul_one]
  have hxv : x * u ^ 4 = u ^ 4 * x := by
    have h := conj_pow_inv hxu 4
    rw [hvinv] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hyv : y * u ^ 4 = u ^ 4 * y := by
    have h := conj_pow_inv hyu 4
    rw [hvinv] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hconjv : ∀ w : G, w * w = 1 → w * u * w⁻¹ = u⁻¹ → IsConj w (w * u ^ 4) := by
    intro w hww hwu
    refine isConj_iff.mpr ⟨u ^ 2, ?_⟩
    have h2 := pow_mul_inv_of_inv hww hwu 2
    calc u ^ 2 * w * (u ^ 2)⁻¹ = w * (u ^ 2)⁻¹ * (u ^ 2)⁻¹ := by rw [h2]
      _ = w * (u ^ 2 * u ^ 2)⁻¹ := by rw [mul_assoc, mul_inv_rev]
      _ = w * u ^ 4 := by rw [← pow_add, show 2 + 2 = 4 from rfl, hvinv]
  obtain ⟨V, hVZ, hvV⟩ := exists_isZConjugate_mem hz hvc
  have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
    hVZ.mem_normalizer_of_commute H hv1 hvV hxv
  have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
    hVZ.mem_normalizer_of_commute H hv1 hvV hyv
  obtain ⟨c, rfl⟩ := hVZ
  rw [normalizer_conj_eq H c] at hxN hyN
  have hSEc := hSE.conj c
  have hc3c := hc3.conj c
  have H' : StrothHyp (conjSubgroup c M) (conjSubgroup c Q) (conjSubgroup c Z) :=
    hSEc.toCfg.ctx.hyp
  have hxQc : x ∈ conjSubgroup c Q := by
    by_contra hxQc
    exact hNF G _ _ _ _ IH hSEc hc3c _ hvV hv1 x hxN hxQc (hvc.symm.trans hxc) _ hvV hv1
      (hconjv x hxx hxu)
  have hyQc : y ∈ conjSubgroup c Q := by
    by_contra hyQc
    exact hNF G _ _ _ _ IH hSEc hc3c _ hvV hv1 y hyN hyQc (hvc.symm.trans hyc) _ hvV hv1
      (hconjv y hyy hyu)
  have hxyQ : u ∈ conjSubgroup c Q := by
    rw [hu]; exact (conjSubgroup c Q).mul_mem hxQc hyQc
  have h2 := Z_sq H' (sq_mem_Z H' hxyQ)
  apply hv1
  calc u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := h2

end Four

end CFSG.RankThree.GF2n.Smith81.E3LRoot
