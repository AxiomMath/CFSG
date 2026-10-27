module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMod
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMinkowski
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassLagrAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration CFSG.StandardType.ExcMaxToral CFSG.RankThree.E6
open scoped Matrix

theorem rckExc_weyl_lagrangian
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (w : WeylGroup .E8) (d : ℕ)
    (hd : d = 3 ∨ d = 4 ∨ d = 6) (lam : ZMod p) (hlam : orderOf lam = d)
    (hge : p ^ 4 ≤ Nat.card {z : Fin Tag.E8.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = lam • z}) :
    ∀ u : Fin Tag.E8.rank → ℤ, w • (w • u) + u = rckChebC d • (w • u) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlam0, hlam2, hsum, hp5⟩ := rckCL_lam_facts hp hp2 hd hlam
  let B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod p) := modMat p Tag.E8.symmetrizedCartan
  let N : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod p) := modMat p (weylMatrix w)
  let N' : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod p) := modMat p (weylMatrix w⁻¹)
  have hiso : Nᵀ * B * N = B := by
    have hZ := ExcFramesHalf.weylMatrix_transpose_mul_symmetrizedCartan_mul w
    have hmap := congrArg (fun X : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ =>
      X.map (Int.castRingHom (ZMod p))) hZ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [N, B, modMat, mul_assoc] using hmap
  have hNN' : N * N' = 1 := by
    show modMat p (weylMatrix w) * modMat p (weylMatrix w⁻¹) = 1
    rw [← rckCL_modMat_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one,
      rckCL_modMat_one]
  have hN'N : N' * N = 1 := by
    show modMat p (weylMatrix w⁻¹) * modMat p (weylMatrix w) = 1
    rw [← rckCL_modMat_mul, ← weylMatrix_mul, inv_mul_cancel, weylMatrix_one,
      rckCL_modMat_one]
  have hBdet : B.det ≠ 0 := by
    have hmap : B.det = ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod p) := by
      have := (RingHom.map_det (Int.castRingHom (ZMod p)) Tag.E8.symmetrizedCartan).symm
      simpa [B, modMat] using this
    rw [hmap]
    have hsym : Tag.E8.symmetrizedCartan.det = 1 := by
      have h : Tag.E8.symmetrizedCartan = Tag.cartan Tag.E8 := by
        simp [Tag.symmetrizedCartan, Tag.symmetrizer]
      rw [h]; exact CFSG.LieType.Chevalley.det_cartan_E8
    rw [hsym, Int.cast_one]
    exact one_ne_zero
  have h4 : 4 ≤ Module.finrank (ZMod p) (LinearMap.ker (Nᵀ - lam • 1).mulVecLin) := by
    have hge' : Nat.card (ZMod p) ^ 4 ≤ Nat.card {z : Fin Tag.E8.rank → ZMod p //
        Nᵀ *ᵥ z = lam • z} := by
      rw [Nat.card_zmod]
      exact hge
    exact rckCL_finrank_ge_of_card (M := Nᵀ) (k := 4) hge'
  have hquad := rckCL_quadratic_of_isometry B N N' hBdet hiso hNN' hN'N hlam0 hlam2 h4
  have hquadc : N * N - (rckChebC d : ZMod p) • N + 1 = 0 := by
    rw [hsum] at hquad; exact hquad
  have hNd : N ^ d = 1 := by
    rcases hd with rfl | rfl | rfl
    · have h0 : N * N + N + 1 = 0 := by
        have h := hquadc
        rw [show (rckChebC 3 : ZMod p) = -1 by norm_num [rckChebC], neg_one_smul,
          sub_neg_eq_add] at h
        exact h
      have h : (N - 1) * (N * N + N + 1) = N ^ 3 - 1 := by noncomm_ring
      rw [h0, mul_zero] at h
      exact sub_eq_zero.mp h.symm
    · have h0 : N * N + 1 = 0 := by
        have h := hquadc
        rw [show (rckChebC 4 : ZMod p) = 0 by norm_num [rckChebC], zero_smul, sub_zero] at h
        exact h
      have h : (N * N - 1) * (N * N + 1) = N ^ 4 - 1 := by noncomm_ring
      rw [h0, mul_zero] at h
      exact sub_eq_zero.mp h.symm
    · have h0 : N * N - N + 1 = 0 := by
        have h := hquadc
        rw [show (rckChebC 6 : ZMod p) = 1 by norm_num [rckChebC], one_smul] at h
        exact h
      have h3 : N ^ 3 + 1 = 0 := by
        have h : N ^ 3 + 1 = (N + 1) * (N * N - N + 1) := by noncomm_ring
        rw [h, h0, mul_zero]
      have h : (N ^ 3 + 1) * (N ^ 3 - 1) = N ^ 6 - 1 := by noncomm_ring
      rw [h3, zero_mul] at h
      exact sub_eq_zero.mp h.symm
  have hY0 : (weylMatrix w) * (weylMatrix w) - (rckChebC d) • (weylMatrix w) + 1 = 0 := by
    refine rckCL_descent hp hp5 hd ?_ ?_
    · have hmodd : modMat p (weylMatrix (w ^ d)) = 1 := by
        rw [weylMatrix_pow]
        change modMat p ((weylMatrix w) ^ d) = 1
        rw [rckCL_modMat_pow]
        exact hNd
      have hwd : w ^ d = 1 :=
        ExcFramesHalf.eq_one_of_modMat_weylMatrix_eq_one (Or.inr rfl) (by omega : 3 ≤ p) hmodd
      have := congrArg weylMatrix hwd
      rwa [weylMatrix_pow, weylMatrix_one] at this
    · intro i j
      have hmod : modMat p ((weylMatrix w) * (weylMatrix w)
          - (rckChebC d) • (weylMatrix w) + 1) = 0 := by
        rw [rckCL_modMat_quadratic]
        exact hquadc
      have h := congrFun (congrFun hmod i) j
      rw [modMat, Matrix.map_apply, Matrix.zero_apply] at h
      have h' : ((((weylMatrix w) * (weylMatrix w) - (rckChebC d) • (weylMatrix w) + 1) i j : ℤ)
          : ZMod p) = 0 := by
        simpa [Matrix.map_apply] using h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h'
  intro u
  have h : ((weylMatrix w) * (weylMatrix w) - (rckChebC d) • (weylMatrix w) + 1) *ᵥ u = 0 := by
    rw [hY0]; simp
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, weylMatrix_mulVec, weylMatrix_mulVec] at h
  rw [sub_add_eq_add_sub] at h
  exact sub_eq_zero.mp h

end CFSG.StandardType.RCKRP
