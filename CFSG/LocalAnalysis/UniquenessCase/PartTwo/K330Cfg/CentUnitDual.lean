module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open scoped Matrix

private lemma k330c_finrank_ker_toLin' {n : ℕ} {F : Type} [Field F]
    (M : Matrix (Fin n) (Fin n) F) :
    Module.finrank F ↥(LinearMap.ker (Matrix.toLin' M)) = n - M.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have hrank : M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.toLin'_apply']
    rfl
  rw [← hrank] at h
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

private lemma k330c_finrank_ker_map_eq {n : ℕ} {F : Type} [Field F] [Finite F]
    (σ : F →+* F) (M : Matrix (Fin n) (Fin n) F) :
    Module.finrank F ↥(LinearMap.ker (Matrix.toLin' (M.map σ))) =
      Module.finrank F ↥(LinearMap.ker (Matrix.toLin' M)) := by
  have hσinj : Function.Injective σ := RingHom.injective σ
  have hσbij : Function.Bijective σ := hσinj.bijective_of_nat_card_le le_rfl
  let Φ : (Fin n → F) ≃ (Fin n → F) := Equiv.piCongrRight fun _ => Equiv.ofBijective σ hσbij
  have hΦ : ∀ v, Φ v = σ ∘ v := fun _ => rfl
  have hmap : ∀ v, (M.map σ) *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec σ M v i).symm
  have hker : ∀ v, v ∈ LinearMap.ker (Matrix.toLin' M) ↔
      Φ v ∈ LinearMap.ker (Matrix.toLin' (M.map σ)) := by
    intro v
    rw [hΦ]
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [hmap v]
    constructor
    · intro h
      rw [h]
      ext i
      simp
    · intro h
      funext i
      exact hσinj (by
        simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun h i)
  have hcard : Nat.card ↥(LinearMap.ker (Matrix.toLin' (M.map σ))) =
      Nat.card ↥(LinearMap.ker (Matrix.toLin' M)) :=
    (Nat.card_congr (Equiv.subtypeEquiv Φ hker)).symm
  have hF : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hpow : Nat.card F ^ Module.finrank F ↥(LinearMap.ker (Matrix.toLin' (M.map σ))) =
      Nat.card F ^ Module.finrank F ↥(LinearMap.ker (Matrix.toLin' M)) := by
    rw [← Module.natCard_eq_pow_finrank (K := F)
          (V := ↥(LinearMap.ker (Matrix.toLin' (M.map σ)))),
        ← Module.natCard_eq_pow_finrank (K := F)
          (V := ↥(LinearMap.ker (Matrix.toLin' M)))]
    exact hcard
  exact Nat.pow_right_injective hF hpow

private lemma k330c_rank_map_eq {n : ℕ} {F : Type} [Field F] [Finite F]
    (σ : F →+* F) (M : Matrix (Fin n) (Fin n) F) :
    (M.map σ).rank = M.rank := by
  have h := k330c_finrank_ker_map_eq σ M
  rw [k330c_finrank_ker_toLin', k330c_finrank_ker_toLin'] at h
  have h1 : (M.map σ).rank ≤ n := Matrix.rank_le_height _
  have h2 : M.rank ≤ n := Matrix.rank_le_height _
  omega

theorem finrank_ker_unitary_eq {n q : ℕ} {F : Type} [Field F] [Finite F] (σ : F →+* F)
    (hσ : ∀ a, σ a = a ^ q) {A : Matrix (Fin n) (Fin n) F}
    (hA : (A.map (· ^ q))ᵀ * A = 1) {ω : F} (hω : ω ^ 3 = 1) (hωq : ω ^ q = ω) :
    Module.finrank F ↥(LinearMap.ker (Matrix.toLin' A -
        ω • (1 : (Fin n → F) →ₗ[F] (Fin n → F)))) =
      Module.finrank F ↥(LinearMap.ker (Matrix.toLin' A -
        ω ^ 2 • (1 : (Fin n → F) →ₗ[F] (Fin n → F)))) := by
  have hmapA' : A.map (· ^ q) = A.map σ := by
    ext i j
    simp [hσ]
  have hA' : (A.map σ)ᵀ * A = 1 := by
    rw [← hmapA']
    exact hA
  have hAinv : A⁻¹ = (A.map σ)ᵀ := Matrix.inv_eq_left_inv hA'
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hA'
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω
    norm_num at hω
  have hω3 : ω * ω ^ 2 = 1 := by
    rw [← pow_succ']
    exact hω
  have hωinv : ω⁻¹ = ω ^ 2 := by
    calc ω⁻¹ = ω⁻¹ * 1 := (mul_one _).symm
      _ = ω⁻¹ * (ω * ω ^ 2) := by rw [hω3]
      _ = ω⁻¹ * ω * ω ^ 2 := by rw [mul_assoc]
      _ = 1 * ω ^ 2 := by rw [inv_mul_cancel₀ hω0]
      _ = ω ^ 2 := one_mul _
  have hσω2 : σ (ω ^ 2) = ω ^ 2 := by
    rw [map_pow, hσ ω, hωq]
  have hfac : A - ω • 1 = (-ω) • (A * (A⁻¹ - ω⁻¹ • 1)) := by
    have h2 : (-ω) * ω⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel₀ hω0]
    have h3 : A * (A⁻¹ - ω⁻¹ • 1) = 1 - ω⁻¹ • A := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_nonsing_inv A hunit]
    rw [h3, smul_sub, smul_smul, h2]
    module
  have hmapσ : A.map σ - ω ^ 2 • 1 = (A - ω ^ 2 • 1).map σ := by
    rw [Matrix.map_sub σ (fun a b => map_sub σ a b),
      Matrix.map_smul σ (ω ^ 2) (fun a => by rw [smul_eq_mul, map_mul, hσω2, smul_eq_mul]),
      Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hrank : (A - ω • 1).rank = (A - ω ^ 2 • 1).rank := by
    calc (A - ω • 1).rank
        = ((-ω) • (A * (A⁻¹ - ω⁻¹ • 1))).rank := by rw [hfac]
      _ = (A * (A⁻¹ - ω⁻¹ • 1)).rank := by
            rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
              (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr hω0))]
      _ = (A⁻¹ - ω⁻¹ • 1).rank := by
            rw [Matrix.rank_mul_eq_right_of_isUnit_det A _ hunit]
      _ = (A⁻¹ - ω ^ 2 • 1).rank := by rw [hωinv]
      _ = ((A.map σ)ᵀ - ω ^ 2 • 1).rank := by rw [hAinv]
      _ = ((A.map σ - ω ^ 2 • 1)ᵀ).rank := by
            rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
      _ = (A.map σ - ω ^ 2 • 1).rank := by rw [Matrix.rank_transpose]
      _ = ((A - ω ^ 2 • 1).map σ).rank := by rw [hmapσ]
      _ = (A - ω ^ 2 • 1).rank := k330c_rank_map_eq σ (A - ω ^ 2 • 1)
  have htoLin₁ : Matrix.toLin' (A - ω • 1) = Matrix.toLin' A - ω • 1 := by
    rw [map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
  have htoLin₂ : Matrix.toLin' (A - ω ^ 2 • 1) = Matrix.toLin' A - ω ^ 2 • 1 := by
    rw [map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
  rw [← htoLin₁, ← htoLin₂, k330c_finrank_ker_toLin', k330c_finrank_ker_toLin', hrank]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
