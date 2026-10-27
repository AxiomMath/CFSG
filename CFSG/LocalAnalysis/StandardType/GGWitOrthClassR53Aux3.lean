module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR53Aux2
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem owR53_polar_wss {K : Type*} [CommRing K] {d : ℕ} (w : Fin d → K) (x y : Fin d → K) :
    QuadraticMap.polar (QuadraticMap.weightedSumSquares K w) x y =
      2 * ∑ i, w i * (x i * y i) := by
  simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem owR53_orthRefl_wss {K : Type*} [Field K] {d : ℕ} (w : Fin d → K) (c : K)
    (a v : Fin d → K) (hc : c ≠ 0) (hQa : QuadraticMap.weightedSumSquares K w a = c) :
    owCr_orthRefl (QuadraticMap.weightedSumSquares K w) a (by rw [hQa]; exact hc) v =
      v - ((2 * c⁻¹) * ∑ i, w i * (v i * a i)) • a := by
  rw [owCr_orthRefl_apply, QuadraticMap.polarBilin_apply_apply, owR53_polar_wss, hQa,
    div_eq_mul_inv]
  congr 1
  ring_nf

theorem owR53_neg_half (w : Fin 3 → ZMod 5) (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) (h2 : w 2 ≠ 0)
    (c : ZMod 5) (hc : c ≠ 0) (hsq : IsSquare (-(w 0 * w 1 * w 2) * c)) :
    WitNEG3 5 (closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c)) := by
  obtain ⟨hA0, hA1, hA2, -, -, -⟩ := owR53_neg_scal w h0 h1 h2 c hc hsq
  let Q : QuadraticForm (ZMod 5) (Fin 3 → ZMod 5) := QuadraticMap.weightedSumSquares (ZMod 5) w
  have hQ0 : Q (owR53_triple w c 0) = c := by
    change QuadraticMap.weightedSumSquares (ZMod 5) w (owR53_triple w c 0) = c
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] using hA0
  have hQ1 : Q (owR53_triple w c 1) = c := by
    change QuadraticMap.weightedSumSquares (ZMod 5) w (owR53_triple w c 1) = c
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] using hA1
  have hQ2 : Q (owR53_triple w c 2) = c := by
    change QuadraticMap.weightedSumSquares (ZMod 5) w (owR53_triple w c 2) = c
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] using hA2
  let s0 : (Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5) :=
    @owCr_orthRefl (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) (Fin 3 → ZMod 5) _ _ Q
      (owR53_triple w c 0) (by rw [hQ0]; exact hc)
  let s1 : (Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5) :=
    @owCr_orthRefl (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) (Fin 3 → ZMod 5) _ _ Q
      (owR53_triple w c 1) (by rw [hQ1]; exact hc)
  let s2 : (Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5) :=
    @owCr_orthRefl (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) (Fin 3 → ZMod 5) _ _ Q
      (owR53_triple w c 2) (by rw [hQ2]; exact hc)
  have hs0 : ∀ v, s0 v = owR53_rf w c (owR53_triple w c 0) v := fun v =>
    @owR53_orthRefl_wss (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) 3 w c
      (owR53_triple w c 0) v hc hQ0
  have hs1 : ∀ v, s1 v = owR53_rf w c (owR53_triple w c 1) v := fun v =>
    @owR53_orthRefl_wss (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) 3 w c
      (owR53_triple w c 1) v hc hQ1
  have hs2 : ∀ v, s2 v = owR53_rf w c (owR53_triple w c 2) v := fun v =>
    @owR53_orthRefl_wss (ZMod 5) (@ZMod.instField 5 ⟨by norm_num⟩) 3 w c
      (owR53_triple w c 2) v hc hQ2
  have hmem0 : s0 ∈ ClassRefl 5 Q c := by
    rw [wit_coord_classRefl_iff (p := 5) (by norm_num) (by norm_num) w c hc]
    exact ⟨owR53_triple w c 0, by simpa only [QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul] using hA0, fun v => by rw [hs0 v]; rfl⟩
  have hmem1 : s1 ∈ ClassRefl 5 Q c := by
    rw [wit_coord_classRefl_iff (p := 5) (by norm_num) (by norm_num) w c hc]
    exact ⟨owR53_triple w c 1, by simpa only [QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul] using hA1, fun v => by rw [hs1 v]; rfl⟩
  have hmem2 : s2 ∈ ClassRefl 5 Q c := by
    rw [wit_coord_classRefl_iff (p := 5) (by norm_num) (by norm_num) w c hc]
    exact ⟨owR53_triple w c 2, by simpa only [QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul] using hA2, fun v => by rw [hs2 v]; rfl⟩
  have hprod : s0 * s1 * s2 = LinearEquiv.neg (ZMod 5) := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
    change s0 (s1 (s2 v)) = -v
    rw [hs0, hs1, hs2]
    exact owR53_neg_prod w h0 h1 h2 c hc hsq v
  refine ⟨?_, ?_⟩
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · rw [← hprod]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hmem0)
      (Subgroup.subset_closure hmem1)) (Subgroup.subset_closure hmem2)

end CFSG.StandardType.ZS

end
