module

public import CFSG.RankThree.PartOne.K159.KleinModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix CFSG.RankThree.PartOne.K159

variable {K : Type*} [Field K]

theorem specialLinearGroup_transvection_smul {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : K)
    (x : Fin n → K) :
    Matrix.SpecialLinearGroup.transvection hij c • x = x + (c * x j) • Pi.single i (1 : K) := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  show (Matrix.transvection i j c) *ᵥ x = x + (c * x j) • Pi.single i (1 : K)
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]

theorem dotProduct_alt_mulVec_self (w : Fin 3 ⊕ Fin 3 → K) (ℓ : Fin 4 → K) :
    ℓ ⬝ᵥ (Klein.alt w *ᵥ ℓ) = 0 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem cong_one_add_smul_vecMulVec (a ℓ : Fin 4 → K) (c : K) (w : Fin 3 ⊕ Fin 3 → K) :
    Klein.cong (1 + c • vecMulVec a ℓ) w =
      w + c • Klein.coords (vecMulVec a ℓ * Klein.alt w + Klein.alt w * (vecMulVec a ℓ)ᵀ) := by
  set N := vecMulVec a ℓ with hN
  set X := Klein.alt w with hX
  have hNXN : N * X * Nᵀ = 0 := by
    have h0 := dotProduct_alt_mulVec_self w ℓ
    ext i j
    have e : (N * X * Nᵀ) i j = a i * a j * (ℓ ⬝ᵥ (X *ᵥ ℓ)) := by
      simp only [hN, Matrix.mul_apply, vecMulVec, Matrix.of_apply, Matrix.transpose_apply,
        dotProduct, Matrix.mulVec, Fin.sum_univ_four]
      ring
    rw [e, show ℓ ⬝ᵥ (X *ᵥ ℓ) = 0 from h0, mul_zero, Matrix.zero_apply]
  have e : (1 + c • N) * X * (1 + c • N)ᵀ = X + c • (N * X + X * Nᵀ) + (c * c) • (N * X * Nᵀ) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_smul, Matrix.mul_assoc]
    abel
  rw [Klein.cong_apply, e, hNXN, smul_zero, add_zero, Klein.coords_add, Klein.coords_smul, hX,
    Klein.coords_alt]

variable [CharP K 2]

theorem ringEquiv_eq_refl_of_kleinTwist (τ : K ≃+* K) (A : (Fin 4 → K) ≃+ (Fin 4 → K))
    (hAτ : ∀ (c : K) (v : Fin 4 → K), A (c • v) = τ c • A v)
    (σ : K → Matrix.SpecialLinearGroup (Fin 4) K)
    (hσ : ∀ (t : K) (v : Fin 4 → K),
      A (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) t • v) =
        σ t • A v)
    (Bt : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (hB : ∀ (t : K) (w : Fin 3 ⊕ Fin 3 → K),
      Bt (Klein.rho (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) t)
        w) = Klein.rho (σ t) (Bt w)) :
    τ = RingEquiv.refl K := by
  classical
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  set e₀ : Fin 4 → K := Pi.single 0 1 with he₀
  set e₁ : Fin 4 → K := Pi.single 1 1 with he₁
  set a : Fin 4 → K := A e₀ with ha
  have hAsymm : ∀ (c : K) (w : Fin 4 → K), A.symm (c • w) = τ.symm c • A.symm w := by
    intro c w
    apply A.injective
    rw [AddEquiv.apply_symm_apply, hAτ, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let lam : (Fin 4 → K) →ₗ[K] K :=
    { toFun := fun w => τ (A.symm w 1)
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        rw [hAsymm, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul,
          RingHom.id_apply] }
  have hlam : ∀ w, lam w = τ (A.symm w 1) := fun w => rfl
  set ℓ : Fin 4 → K := fun i => lam (Pi.single i 1) with hℓ
  have hlamℓ : ∀ w, lam w = ℓ ⬝ᵥ w := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ lam w, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm, hℓ]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hσmat : ∀ t : K, ((σ t : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      1 + τ t • vecMulVec a ℓ := by
    intro t
    rw [Matrix.ext_iff_mulVec]
    intro w
    have h1 : (σ t : Matrix (Fin 4) (Fin 4) K) *ᵥ w = σ t • w := rfl
    rw [h1]
    obtain ⟨v, rfl⟩ : ∃ v, w = A v := ⟨A.symm w, (A.apply_symm_apply w).symm⟩
    rw [← hσ, specialLinearGroup_transvection_smul h01 t v, map_add, hAτ, ← ha]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    congr 1
    have h2 : vecMulVec a ℓ *ᵥ A v = (ℓ ⬝ᵥ A v) • a := by
      ext i
      simp [Matrix.mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    rw [h2, ← hlamℓ, hlam, AddEquiv.symm_apply_apply, smul_smul, map_mul]
  let P : Matrix (Fin 4) (Fin 4) K → (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K) :=
    fun N w => Klein.coords (N * Klein.alt w + Klein.alt w * Nᵀ)
  have hu : ∀ t : K, ((Matrix.SpecialLinearGroup.transvection h01 t :
      Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        1 + t • vecMulVec e₀ e₁ := by
    intro t
    show Matrix.transvection 0 1 t = _
    rw [Matrix.transvection]
    congr 1
    ext i j
    by_cases h1 : i = 0 <;> by_cases h2 : j = 1 <;>
      simp [vecMulVec, Matrix.single_apply, he₀, he₁, Pi.single_apply, h1, h2, eq_comm]
  have hρu : ∀ t w, Klein.rho (Matrix.SpecialLinearGroup.transvection h01 t) w =
      w + t • P (vecMulVec e₀ e₁) w := fun t w => by
    rw [Klein.rho_apply, hu, cong_one_add_smul_vecMulVec]
  have hρσ : ∀ t w, Klein.rho (σ t) w = w + τ t • P (vecMulVec a ℓ) w := fun t w => by
    rw [Klein.rho_apply, hσmat, cong_one_add_smul_vecMulVec]
  have hkey : ∀ t w, t • Bt (P (vecMulVec e₀ e₁) w) = τ t • P (vecMulVec a ℓ) (Bt w) := by
    intro t w
    have h := hB t w
    rw [hρu, hρσ, map_add, map_smul] at h
    exact add_left_cancel h
  have hone : ∀ w, Bt (P (vecMulVec e₀ e₁) w) = P (vecMulVec a ℓ) (Bt w) := fun w => by
    simpa using hkey 1 w
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t : K, τ t ≠ t := by
    by_contra h
    push Not at h
    exact hne (RingEquiv.ext h)
  have hzero : ∀ w, Bt (P (vecMulVec e₀ e₁) w) = 0 := by
    intro w
    have h1 := hkey t w
    rw [← hone] at h1
    have h2 : (t - τ t) • Bt (P (vecMulVec e₀ e₁) w) = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm ht))
  have hP : P (vecMulVec e₀ e₁) (Pi.single (Sum.inr 2) 1) (Sum.inl 1) = 1 := by
    simp [P, Klein.coords, Klein.alt, CFSG.LocalAnalysis.antiMat, vecMulVec, he₀, he₁,
      Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Matrix.of_apply]
  have h0 := hzero (Pi.single (Sum.inr 2) 1)
  rw [map_eq_zero_iff Bt Bt.injective] at h0
  rw [h0] at hP
  exact zero_ne_one hP

end CFSG.RankThree.GF2n.Stroth80
