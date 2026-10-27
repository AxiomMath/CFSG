module

public import CFSG.Quasithin.Vol2.Ch10SecV1SA

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open scoped Matrix

variable {K : Type} [Field K]

@[expose] def sv (σ : K →+* K) (x : Fin 3 → K) : Fin 3 → K := fun i => σ (x i)

theorem sv_mulVec (σ : K →+* K) (M : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) :
    sv σ (M *ᵥ x) = M.map σ *ᵥ sv σ x :=
  funext fun i => RingHom.map_mulVec σ M x i

theorem fix_of_pow_three {σ : K →+* K} (hσ : ∀ a, σ (σ (σ a)) = a) {ω : K} (hω : ω ^ 3 = 1) :
    σ ω = ω := by
  by_cases h1 : ω = 1
  · rw [h1, map_one]
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)
  set x := σ ω with hx
  have hxq : x ^ 2 + x + 1 = 0 := by
    rw [hx, ← map_pow, ← map_one σ, ← map_add, ← map_add, hq, map_zero]
  have hfac : (x - ω) * (x - ω ^ 2) = 0 := by linear_combination hxq - x * hq + hω
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hx' : x = ω ^ 2 := sub_eq_zero.mp h
    have h2 : σ (ω ^ 2) = ω := by
      rw [map_pow, ← hx, hx', ← pow_mul,
        show ω ^ (2 * 2) = ω * ω ^ 3 by ring, hω, mul_one]
    have h3 : σ (σ (σ ω)) = ω ^ 2 := by
      rw [← hx, hx', h2, ← hx, hx']
    rw [hσ] at h3
    have : ω * (ω - 1) = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [h0] at hω
      norm_num at hω
    · exact h1 (sub_eq_zero.mp h0)

theorem pow_three_eq {σ : K →+* K} {T : (Fin 3 → K) → (Fin 3 → K)}
    (hTsemi : ∀ (a : K) x, T (a • x) = σ a • T x) {N : Matrix (Fin 3) (Fin 3) K} (hN : N.det = 1)
    (hT3 : ∀ x, T (T (T x)) = N *ᵥ x) (a : K) : σ (σ (σ a)) = a := by
  set x₀ : Fin 3 → K := N⁻¹ *ᵥ Pi.single 0 1 with hx₀def
  have hx₀ : T (T (T x₀)) = Pi.single 0 1 := by
    rw [hT3, hx₀def, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (by rw [hN]; exact isUnit_one), Matrix.one_mulVec]
  have h1 : T (T (T (a • x₀))) = σ (σ (σ a)) • T (T (T x₀)) := by rw [hTsemi, hTsemi, hTsemi]
  have h2 : T (T (T (a • x₀))) = a • T (T (T x₀)) := by rw [hT3, hT3, Matrix.mulVec_smul]
  rw [hx₀] at h1 h2
  have := congrFun (h1.symm.trans h2) 0
  simpa using this

theorem cube_eq {σ : K →+* K} (hσ3 : ∀ a, σ (σ (σ a)) = a) (D : Matrix (Fin 3) (Fin 3) K)
    (x : Fin 3 → K) :
    D *ᵥ sv σ (D *ᵥ sv σ (D *ᵥ sv σ x)) = (D * D.map σ * (D.map σ).map σ) *ᵥ x := by
  have hs : sv σ (sv σ (sv σ x)) = x := funext fun i => hσ3 (x i)
  rw [sv_mulVec, sv_mulVec, sv_mulVec, hs, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem exists_B {σ : K →+* K} {T : (Fin 3 → K) → (Fin 3 → K)}
    (hTadd : ∀ x y, T (x + y) = T x + T y) (hTsemi : ∀ (a : K) x, T (a • x) = σ a • T x)
    {N : Matrix (Fin 3) (Fin 3) K} (hN : N.det = 1) (hT3 : ∀ x, T (T (T x)) = N *ᵥ x) :
    ∃ P : Matrix (Fin 3) (Fin 3) K, P.det = 1 ∧
      (∀ x, P *ᵥ T (P *ᵥ T (P *ᵥ T x)) = x) ∧
      ∀ d : Fin 3 → K, (∀ i, σ (d i) = d i) →
        ∀ x, P *ᵥ T (Matrix.diagonal d *ᵥ x) = Matrix.diagonal d *ᵥ (P *ᵥ T x) := by
  have hσ3 := pow_three_eq hTsemi hN hT3
  have hsv : ∀ x, sv (σ.comp σ) (sv σ x) = x := fun x => funext fun i => hσ3 (x i)
  let A : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun x => T (sv (σ.comp σ) x)
      map_add' := fun x y => by
        show T (sv _ (x + y)) = T (sv _ x) + T (sv _ y)
        rw [show sv (σ.comp σ) (x + y) = sv (σ.comp σ) x + sv (σ.comp σ) y from
          funext fun i => map_add _ _ _, hTadd]
      map_smul' := fun a x => by
        show T (sv _ (a • x)) = a • T (sv _ x)
        rw [show sv (σ.comp σ) (a • x) = σ (σ a) • sv (σ.comp σ) x from
          funext fun i => by simp [sv], hTsemi, hσ3] }
  set M := LinearMap.toMatrix' A with hMdef
  have hT : ∀ x, T x = M *ᵥ sv σ x := fun x => by
    rw [hMdef, LinearMap.toMatrix'_mulVec]
    show T x = T (sv (σ.comp σ) (sv σ x))
    rw [hsv]
  have hMN : M * M.map σ * (M.map σ).map σ = N := by
    refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← cube_eq hσ3, ← hT, ← hT, ← hT, hT3]
  have hdet : M.det * σ M.det * σ (σ M.det) = 1 := by
    have e1 : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    have e2 : ((M.map σ).map σ).det = σ (σ M.det) := by
      rw [← e1]
      exact (RingHom.map_det σ _).symm
    have := congrArg Matrix.det hMN
    rwa [Matrix.det_mul, Matrix.det_mul, e1, e2, hN] at this
  have ha : M.det ≠ 0 := fun h0 => by
    rw [h0, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  set D := Matrix.diagonal ![M.det, 1, 1] with hD
  have hB : ∀ x, (D * M⁻¹) *ᵥ T x = D *ᵥ sv σ x := fun x => by
    rw [hT, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ha), Matrix.mul_one]
  refine ⟨D * M⁻¹, ?_, ?_, fun d hd x => ?_⟩
  · rw [Matrix.det_mul, hD, Matrix.det_diagonal, Fin.prod_univ_three, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    simp [ha]
  · intro x
    rw [hB, hB, hB, cube_eq hσ3]
    have hD3 : D * D.map σ * (D.map σ).map σ = 1 := by
      rw [hD, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_map (map_zero σ),
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i
      · simpa using hdet
      · simp
      · simp
    rw [hD3, Matrix.one_mulVec]
  · rw [hB, hB, sv_mulVec, Matrix.diagonal_map (map_zero σ),
      show (fun i => σ (d i)) = d from funext hd, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
