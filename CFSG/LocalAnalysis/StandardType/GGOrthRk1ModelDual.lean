module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Model
import CFSG.LocalAnalysis.StandardType.GGOrthRk1ModelTwo
import Mathlib.LinearAlgebra.Center

public section

open Module Matrix

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D]

private noncomputable def cM (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  Matrix.SpecialLinearGroup.toLin' M

private theorem exists_linearIndependent_cM (M : Matrix.SpecialLinearGroup (Fin 2) K)
    (hM1 : M ≠ 1) : ∃ u : Fin 2 → K, LinearIndependent K ![u, cM M u] := by
  by_contra h
  rw [not_exists] at h
  obtain ⟨a, ha⟩ :=
    LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (R := K) (V := Fin 2 → K) h
  have hmat : (M : Matrix (Fin 2) (Fin 2) K) = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : LinearMap.toMatrix' (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) =
        LinearMap.toMatrix' (a • (1 : (Fin 2 → K) →ₗ[K] (Fin 2 → K))) := by rw [ha]
    rw [cM, Matrix.SpecialLinearGroup.toLin'_to_linearMap, map_smul, LinearMap.toMatrix'_one]
      at h1
    simpa using h1
  have hdet : a ^ 2 = 1 := by
    have h := congrArg Matrix.det hmat
    rw [M.2, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
    exact h.symm
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp hdet with h | h
    · exact h
    · rw [CharTwo.neg_eq] at h; exact h
  apply hM1
  apply Subtype.ext
  rw [hmat, ha1, one_smul]
  rfl

private theorem rk1Block_cM (M : Matrix.SpecialLinearGroup (Fin 2) K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hM : M ^ p = 1) (hM1 : M ≠ 1) : Rk1Block (cM M) p := by
  obtain ⟨u₀, hu₀⟩ := exists_linearIndependent_cM M hM1
  let b : Basis (Fin 2) K (Fin 2 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hu₀ (by simp [Module.finrank_fin_fun K])
  have hb0 : b 0 = u₀ := by simp [b]
  have hb1 : b 1 = (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) u₀ := by simp [b]
  set C : Matrix (Fin 2) (Fin 2) K :=
    LinearMap.toMatrix b b (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) with hC
  set t : K := LinearMap.trace K (Fin 2 → K) (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) with ht
  have h00 : C 0 0 = 0 := by
    rw [hC, LinearMap.toMatrix_apply, hb0, ← hb1, Basis.repr_self_apply]
    simp
  have h10 : C 1 0 = 1 := by
    rw [hC, LinearMap.toMatrix_apply, hb0, ← hb1, Basis.repr_self_apply]
    simp
  have h01 : C 0 1 = 1 := by
    have hdetC : Matrix.det C = 1 := by
      rw [hC, LinearMap.det_toMatrix]
      rw [show ((cM M : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
            (Fin 2 → K) →ₗ[K] (Fin 2 → K)) =
          Matrix.toLin' (M : Matrix (Fin 2) (Fin 2) K) from by
        rw [cM, Matrix.SpecialLinearGroup.toLin'_to_linearMap]]
      rw [LinearMap.det_toLin']
      exact M.2
    have h1 := hdetC
    rw [Matrix.det_fin_two] at h1
    rw [h00, h10, zero_mul, mul_one, zero_sub, CharTwo.neg_eq] at h1
    exact h1
  have h11 : C 1 1 = t := by
    have htraceC : Matrix.trace C = t := by
      rw [hC, ht]
      exact (LinearMap.trace_eq_matrix_trace K b _).symm
    have h1 := htraceC
    rw [Matrix.trace_fin_two] at h1
    rw [h00] at h1
    simpa using h1
  have hCe : C = !![0, 1; 1, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have hxp : (cM M : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ^ p = 1 := by
    rw [cM, ← map_pow, hM, map_one]
  have hlinp : (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) ^ p = 1 := by
    have hcoepow : ∀ n : ℕ,
        (((cM M) ^ n : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
          (Fin 2 → K) →ₗ[K] (Fin 2 → K)) =
          ((cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) ^ n) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
    rw [← hcoepow p, hxp]
    rfl
  have ht_ne : t ≠ 0 := by
    intro ht0
    obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
      refine ⟨(p + 1) / 2, ?_⟩
      have : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact h
      omega
    have hC2 : C * C = 1 := by
      rw [hCe, ht0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
    have hCp : C ^ p = 1 := by
      change (LinearMap.toMatrixAlgEquiv b (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K))) ^ p = 1
      rw [← map_pow, hlinp, map_one]
    have hC1 : C = 1 := by
      calc C = C ^ (p + 1) := by rw [pow_succ, hCp, one_mul]
        _ = C ^ (2 * m) := by rw [hm]
        _ = (C ^ 2) ^ m := by rw [pow_mul]
        _ = 1 := by rw [pow_two, hC2, one_pow]
    rw [hC1] at h01
    have hz : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp
    rw [hz] at h01
    exact zero_ne_one h01
  have hfix : ∀ u : Fin 2 → K, cM M u = u → u = 0 := by
    intro u hu
    have hw : C *ᵥ b.repr u = b.repr u := by
      have h := LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b)
        (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) u
      rw [← hC] at h
      rw [h]
      simpa using congrArg b.repr hu
    have hw0 : b.repr u 1 = b.repr u 0 := by
      have h := congrArg (fun z : Fin 2 → K => z 0) hw
      rw [hCe, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at h
      simpa using h
    have hw1 : b.repr u 0 + t * b.repr u 1 = b.repr u 1 := by
      have h := congrArg (fun z : Fin 2 → K => z 1) hw
      rw [hCe, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at h
      simpa using h
    have hzero : b.repr u 1 = 0 := by
      rw [← hw0] at hw1
      have hsum : b.repr u 1 + t * b.repr u 1 = b.repr u 1 + 0 := by
        rw [add_zero]; exact hw1
      have ht1 : t * b.repr u 1 = 0 := add_left_cancel hsum
      exact (mul_eq_zero.mp ht1).resolve_left ht_ne
    have hrep : b.repr u = 0 := by
      ext i
      fin_cases i
      · simpa using (show b.repr u 0 = 0 from by rw [← hw0]; exact hzero)
      · simpa using hzero
    exact b.repr.map_eq_zero_iff.mp hrep
  have htwist : ∃ T : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K), T * cM M * T⁻¹ = (cM M)⁻¹ := by
    let TC : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]
    have hTC2 : TC * TC = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [TC, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
    let Tmap : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := (LinearMap.toMatrixAlgEquiv b).symm TC
    have hTmap_mat : (LinearMap.toMatrixAlgEquiv b) Tmap = TC :=
      (LinearMap.toMatrixAlgEquiv b).apply_symm_apply TC
    have hTmap2 : Tmap * Tmap = 1 := by
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_mul, hTmap_mat, map_one, hTC2]
    have hcomp : Tmap.comp Tmap = LinearMap.id := by
      rw [← Module.End.mul_eq_comp]
      exact hTmap2
    let T : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) := LinearEquiv.ofLinearMap Tmap Tmap hcomp hcomp
    have hmul : cM M * T * cM M = T := by
      apply LinearEquiv.toLinearMap_injective
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
      change ((cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) * Tmap) *
        (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = Tmap
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_mul, map_mul, hTmap_mat,
        show (LinearMap.toMatrixAlgEquiv b) (cM M : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) = C from rfl]
      rw [hCe]
      change (!![0, 1; 1, t] * TC) * !![0, 1; 1, t] = TC
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [TC, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
    refine ⟨T, ?_⟩
    have h1 : cM M * (T * cM M * T⁻¹) = cM M * (cM M)⁻¹ := by
      calc cM M * (T * cM M * T⁻¹) = (cM M * T * cM M) * T⁻¹ := by group
        _ = T * T⁻¹ := by rw [hmul]
        _ = 1 := mul_inv_cancel T
        _ = cM M * (cM M)⁻¹ := (mul_inv_cancel (cM M)).symm
    exact mul_left_cancel h1
  exact ⟨Module.finrank_fin_fun K, hp, hp2,
    by rw [cM, ← map_pow, hM, map_one], hfix, htwist⟩

private noncomputable def transposeE (K : Type) [Field K] :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)) where
  toFun p := (![p.1 0, p.2 0], ![p.1 1, p.2 1])
  invFun p := (![p.1 0, p.2 0], ![p.1 1, p.2 1])
  left_inv p := by ext i <;> fin_cases i <;> rfl
  right_inv p := by ext i <;> fin_cases i <;> rfl
  map_add' p q := by ext i <;> fin_cases i <;> simp
  map_smul' a p := by ext i <;> fin_cases i <;> simp

private noncomputable def sigma (hD : finrank K D = 2) :=
  ((Module.finBasisOfFinrankEq K D hD).equivFun.prodCongr
      (Module.finBasisOfFinrankEq K D hD).equivFun).trans (transposeE K)

omit [CharP K 2] in
private theorem sigma_modelAct (hD : finrank K D = 2)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) (v : D × D) :
    sigma (K := K) hD (rk1ModelAct M v) =
      (cM M (sigma (K := K) hD v).1, cM M (sigma (K := K) hD v).2) := by
  obtain ⟨x, y⟩ := v
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [sigma, transposeE, cM, rk1ModelAct_apply, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
        map_add, map_smul, smul_eq_mul]
  · funext i
    fin_cases i <;>
      simp [sigma, transposeE, cM, rk1ModelAct_apply, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
        map_add, map_smul, smul_eq_mul]

private noncomputable def swapD (hD : finrank K D = 2) :=
  (sigma (K := K) hD).trans
    ((Module.finBasisOfFinrankEq K D hD).equivFun.symm.prodCongr
      (Module.finBasisOfFinrankEq K D hD).equivFun.symm)

omit [CharP K 2] in
private theorem swapD_involutive (hD : finrank K D = 2) (v : D × D) :
    swapD (K := K) hD (swapD (K := K) hD v) = v := by
  obtain ⟨x, y⟩ := v
  apply Prod.ext
  · simp [swapD, sigma, transposeE, LinearEquiv.prodCongr_apply, Basis.equivFun_apply]
    have h := Basis.sum_repr (Module.finBasisOfFinrankEq K D hD) x
    rw [Fin.sum_univ_two] at h
    exact h
  · simp [swapD, sigma, transposeE, LinearEquiv.prodCongr_apply, Basis.equivFun_apply]
    have h := Basis.sum_repr (Module.finBasisOfFinrankEq K D hD) y
    rw [Fin.sum_univ_two] at h
    exact h

private theorem swapD_omega (hD : finrank K D = 2) (x y : D) :
    rk1Omega hD (swapD (K := K) hD (x, y)).1 (swapD (K := K) hD (x, y)).2 =
      rk1Omega hD x y := by
  let b := Module.finBasisOfFinrankEq K D hD
  have h1 : (swapD (K := K) hD (x, y)).1 = (b.repr x 0) • b 0 + (b.repr y 0) • b 1 := by
    simp [swapD, sigma, transposeE, b, Basis.equivFun_symm_apply]
  have h2 : (swapD (K := K) hD (x, y)).2 = (b.repr x 1) • b 0 + (b.repr y 1) • b 1 := by
    simp [swapD, sigma, transposeE, b, Basis.equivFun_symm_apply]
  rw [h1, h2]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [map_add, map_smul, smul_eq_mul, rk1Omega_self, mul_zero, add_zero, zero_add,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [rk1Omega_swap hD (b 1) (b 0)]
  ring

private noncomputable def conjMap (hD : finrank K D = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : D ≃ₗ[K] D :=
  ((Module.finBasisOfFinrankEq K D hD).equivFun.trans (cM g)).trans
    (Module.finBasisOfFinrankEq K D hD).equivFun.symm

omit [CharP K 2] in
private theorem swapD_modelAct (hD : finrank K D = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (w : D × D) :
    swapD (K := K) hD (rk1ModelAct g w) =
      (conjMap (K := K) hD g (swapD (K := K) hD w).1,
       conjMap (K := K) hD g (swapD (K := K) hD w).2) := by
  have h := sigma_modelAct (K := K) (D := D) hD g w
  have hswap : swapD (K := K) hD (rk1ModelAct g w) =
      ((Module.finBasisOfFinrankEq K D hD).equivFun.symm (cM g (sigma (K := K) hD w).1),
       (Module.finBasisOfFinrankEq K D hD).equivFun.symm (cM g (sigma (K := K) hD w).2)) := by
    simp only [swapD, LinearEquiv.trans_apply, h, LinearEquiv.prodCongr_apply]
  have hswap' : swapD (K := K) hD w =
      ((Module.finBasisOfFinrankEq K D hD).equivFun.symm (sigma (K := K) hD w).1,
       (Module.finBasisOfFinrankEq K D hD).equivFun.symm (sigma (K := K) hD w).2) := by
    simp only [swapD, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  rw [hswap, hswap']
  apply Prod.ext <;>
    simp only [conjMap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

omit [CharP K 2] in
private theorem coeToLinearMap_pow {M : Type*} [AddCommGroup M] [Module K M]
    (u : M ≃ₗ[K] M) (n : ℕ) :
    ((u ^ n : M ≃ₗ[K] M) : M →ₗ[K] M) = (u : M →ₗ[K] M) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private noncomputable def conjEquiv
    (c₀ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (e : D ≃ₗ[K] (Fin 2 → K)) : D ≃ₗ[K] D :=
  LinearEquiv.ofLinearMap
    ((LinearEquiv.conjRingEquiv e.symm) (c₀ : Module.End K (Fin 2 → K)))
    ((LinearEquiv.conjRingEquiv e.symm) ((c₀⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
      Module.End K (Fin 2 → K)))
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul, ← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel]
      change (LinearEquiv.conjRingEquiv e.symm) (1 : Module.End K (Fin 2 → K)) = 1
      rw [map_one])
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul, ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel]
      change (LinearEquiv.conjRingEquiv e.symm) (1 : Module.End K (Fin 2 → K)) = 1
      rw [map_one])

omit [FiniteDimensional K D] [CharP K 2] in
private theorem rk1Block_transport (hD : finrank K D = 2)
    {c₀ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {p : ℕ} (hc₀ : Rk1Block c₀ p)
    (e : D ≃ₗ[K] (Fin 2 → K)) : Rk1Block (conjEquiv c₀ e) p := by
  refine ⟨hD, hc₀.prime, hc₀.ne_two, ?_, ?_, ?_⟩
  · apply LinearEquiv.toLinearMap_injective
    rw [coeToLinearMap_pow]
    rw [show (conjEquiv c₀ e : D →ₗ[K] D) =
        (LinearEquiv.conjRingEquiv e.symm) (c₀ : Module.End K (Fin 2 → K)) from rfl]
    rw [← map_pow]
    have hc₀p : (c₀ : Module.End K (Fin 2 → K)) ^ p = 1 := by
      rw [← coeToLinearMap_pow, hc₀.pow_eq, LinearEquiv.coe_toLinearMap_one]
      exact Module.End.one_eq_id.symm
    rw [hc₀p, map_one, LinearEquiv.coe_toLinearMap_one]
    exact Module.End.one_eq_id.symm
  · intro u hu
    have h1 : e.symm (c₀ (e u)) = u := by
      have hh : ((LinearEquiv.conjRingEquiv e.symm) (c₀ : Module.End K (Fin 2 → K))) u = u := by
        simpa [conjEquiv] using hu
      simpa [LinearEquiv.conj_apply_apply] using hh
    have h2 : c₀ (e u) = e u := by
      have hh := congrArg (fun z => e z) h1
      simpa using hh
    have h3 : e u = 0 := hc₀.fix (e u) h2
    exact e.injective (by simpa using h3)
  · obtain ⟨T₀, hT₀⟩ := hc₀.twist
    refine ⟨conjEquiv T₀ e, ?_⟩
    apply LinearEquiv.toLinearMap_injective
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    change ((LinearEquiv.conjRingEquiv e.symm) (T₀ : Module.End K (Fin 2 → K))) *
        ((LinearEquiv.conjRingEquiv e.symm) (c₀ : Module.End K (Fin 2 → K))) *
        ((LinearEquiv.conjRingEquiv e.symm) ((T₀⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
          Module.End K (Fin 2 → K))) =
      ((LinearEquiv.conjRingEquiv e.symm) ((c₀⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
        Module.End K (Fin 2 → K)))
    rw [← map_mul, ← map_mul]
    rw [show (T₀ : Module.End K (Fin 2 → K)) * (c₀ : Module.End K (Fin 2 → K)) *
        ((T₀⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : Module.End K (Fin 2 → K)) =
        ((c₀⁻¹ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) : Module.End K (Fin 2 → K)) from by
      rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hT₀]]

theorem rk1ModelAct_commute_eq (hD : finrank K D = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ^ p = 1) (hM1 : M ≠ 1)
    {h : Module.End K (D × D)}
    (hcomm : ∀ v : D × D, h (rk1ModelAct M v) = rk1ModelAct M (h v))
    (hiso : ∀ v : D × D, rk1Omega hD (h v).1 (h v).2 = rk1Omega hD v.1 v.2)
    {k : ℕ} (hk : h ^ (2 ^ k) = 1) :
    ∃ e : D →ₗ[K] D, ∀ v : D × D, h v = (e v.1, e v.2) := by
  let b := Module.finBasisOfFinrankEq K D hD
  have hceq : conjEquiv (cM M) b.equivFun = conjMap (K := K) hD M := by
    apply LinearEquiv.ext
    intro x
    simp [conjEquiv, conjMap, cM, b]
  have hcM : Rk1Block (cM M) p := rk1Block_cM M hp hp2 hM hM1
  have hc : Rk1Block (conjMap (K := K) hD M) p := by
    rw [← hceq]
    exact rk1Block_transport (K := K) hD hcM b.equivFun
  let S := swapD (K := K) hD
  let h'' : Module.End K (D × D) := (LinearEquiv.conjRingEquiv S) h
  have hsymm : (S.symm : D × D → D × D) = (S : D × D → D × D) := by
    funext y
    exact S.injective (by rw [LinearEquiv.apply_symm_apply, swapD_involutive])
  have h''_apply : ∀ x : D × D, h'' x = S (h (S x)) := by
    intro x
    rw [show h'' x = ((LinearEquiv.conjRingEquiv S) h) x from rfl,
      show ((LinearEquiv.conjRingEquiv S) h) x = (S.conj h) x from rfl,
      LinearEquiv.conj_apply_apply, hsymm]
  have hcomm'' : ∀ v : D × D,
      h'' (conjMap (K := K) hD M v.1, conjMap (K := K) hD M v.2) =
        (conjMap (K := K) hD M (h'' v).1, conjMap (K := K) hD M (h'' v).2) := by
    intro v
    have hv : (conjMap (K := K) hD M v.1, conjMap (K := K) hD M v.2) =
        S (rk1ModelAct M (S v)) := by
      rw [show (conjMap (K := K) hD M v.1, conjMap (K := K) hD M v.2) =
          (conjMap (K := K) hD M (S (S v)).1, conjMap (K := K) hD M (S (S v)).2) from by
        rw [swapD_involutive],
        ← swapD_modelAct (K := K) hD M (S v)]
    rw [hv]
    conv_lhs => rw [h''_apply, swapD_involutive, hcomm (S v),
      swapD_modelAct (K := K) hD M (h (S v)), ← h''_apply v]
  have hiso'' : ∀ v : D × D,
      rk1Omega hD (h'' v).1 (h'' v).2 = rk1Omega hD v.1 v.2 := by
    intro v
    rw [h''_apply, swapD_omega (K := K) hD (h (S v)).1 (h (S v)).2, hiso (S v),
      ← swapD_omega (K := K) hD v.1 v.2]
  have hk'' : h'' ^ (2 ^ k) = 1 := by
    rw [show h'' = (LinearEquiv.conjRingEquiv S) h from rfl, ← map_pow, hk, map_one]
  obtain ⟨g, hg⟩ := Rk1Block.exists_rk1ModelAct hc hcomm'' hiso'' hk''
  refine ⟨conjMap (K := K) hD g, ?_⟩
  intro v
  have h1 : h v = S (h'' (S v)) := by
    rw [h''_apply (S v), swapD_involutive, swapD_involutive]
  rw [h1, hg (S v), swapD_modelAct (K := K) hD g (S v), swapD_involutive]
  rfl

end OrthTorus

end CFSG.StandardType

end
