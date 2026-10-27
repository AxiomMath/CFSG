module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionUnitary

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Matrix

variable {K : Type} [Field K]

theorem diag_conj_entries {A N : Matrix (Fin 3) (Fin 3) K} {c d₀ d₁ d₂ e₀ e₁ e₂ : K}
    (hA10 : A 1 0 = 0) (hA20 : A 2 0 = 0) (hA21 : A 2 1 = 0) (hA0 : A 0 0 ≠ 0)
    (hA1 : A 1 1 ≠ 0) (hA2 : A 2 2 ≠ 0) (hN10 : N 1 0 = 0) (hN20 : N 2 0 = 0)
    (hN21 : N 2 1 = 0) (hN00 : N 0 0 = 1) (hN11 : N 1 1 = 1) (hN22 : N 2 2 = 1)
    (h : A * !![d₀, 0, 0; 0, d₁, 0; 0, 0, d₂] = c • (N * !![e₀, 0, 0; 0, e₁, 0; 0, 0, e₂] * A)) :
    d₀ = c * e₀ ∧ d₁ = c * e₁ ∧ d₂ = c * e₂ := by
  have e : ∀ i j, (A * !![d₀, 0, 0; 0, d₁, 0; 0, 0, d₂]) i j =
      (c • (N * !![e₀, 0, 0; 0, e₁, 0; 0, 0, e₂] * A)) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e00 e11 e22
  simp [hA10, hA20, hA21, hN10, hN20, hN21, hN00, hN11, hN22] at e00 e11 e22
  refine ⟨mul_left_cancel₀ hA0 ?_, mul_left_cancel₀ hA1 ?_, mul_left_cancel₀ hA2 ?_⟩
  · rw [e00]; ring
  · rw [e11]; ring
  · rw [e22]; ring

theorem cube_eq_one_of_torus {c c' x y μ : K} (hc : c ≠ 0) (hc' : c' ≠ 0) (hx : x ≠ 0)
    (h0 : x = μ * c) (h1 : y / x = μ * (c' / c)) (h2 : y⁻¹ = μ * c'⁻¹) : μ ^ 3 = 1 := by
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h0
    exact hx h0
  have hy : y = c' * μ⁻¹ := by
    have : y = (μ * c'⁻¹)⁻¹ := by rw [← h2, inv_inv]
    rw [this, mul_inv, inv_inv, mul_comm]
  rw [hy, h0] at h1
  field_simp at h1
  exact h1.symm

@[expose] def fixedSubfield (σ : K ≃+* K) : Subfield K where
  carrier := {x | σ x = x}
  zero_mem' := map_zero σ
  one_mem' := map_one σ
  add_mem' {x y} hx hy := by
    show σ (x + y) = x + y
    rw [map_add, hx, hy]
  mul_mem' {x y} hx hy := by
    show σ (x * y) = x * y
    rw [map_mul, hx, hy]
  neg_mem' {x} hx := by
    show σ (-x) = -x
    rw [map_neg, hx]
  inv_mem' x hx := by
    show σ x⁻¹ = x⁻¹
    rw [map_inv₀, hx]

theorem eq_refl_of_cube [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ x : K, σ x ^ 3 = x ^ 3) : σ = RingEquiv.refl K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set F := fixedSubfield σ with hF
  set cube : Kˣ →* Kˣ := powMonoidHom 3 with hcube
  have hker : Nat.card cube.ker ≤ 3 := by
    have h1 : cube.ker = rootsOfUnity 3 K := by
      ext u
      simp [hcube, mem_rootsOfUnity]
    rw [h1]
    exact card_rootsOfUnity K 3
  have hrange : Nat.card Kˣ ≤ 3 * Nat.card cube.range := by
    have h := Subgroup.card_mul_index cube.ker
    rw [Subgroup.index_ker] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hker
  have hrF : Nat.card cube.range + 1 ≤ Nat.card F := by
    have : Fintype F := Fintype.ofFinite F
    let ι : cube.range → Fˣ := fun u => Units.mk0 ⟨((u : Kˣ) : K), by
        obtain ⟨v, hv⟩ := u.2
        show σ ((u : Kˣ) : K) = ((u : Kˣ) : K)
        rw [← hv]
        simpa [hcube] using hσ (v : K)⟩ (fun h => (u : Kˣ).ne_zero (congrArg Subtype.val h))
    have hι : Function.Injective ι := fun u v h =>
      Subtype.ext (Units.ext (congrArg (fun w : Fˣ => ((w : F) : K)) h))
    have h1 := Nat.card_le_card_of_injective ι hι
    have h2 : Nat.card Fˣ + 1 = Nat.card F := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units,
        Nat.sub_add_cancel Fintype.card_pos]
    omega
  have hKu : Nat.card Kˣ + 1 = Nat.card K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units,
      Nat.sub_add_cancel Fintype.card_pos]
  by_contra hne
  have hFK : ∃ x : K, x ∉ F := by
    by_contra h
    exact hne (RingEquiv.ext fun x => not_not.mp (fun hx => h ⟨x, hx⟩))
  have hd := Module.natCard_eq_pow_finrank (K := F) (V := K)
  have h2 : 2 ≤ Module.finrank F K := by
    by_contra h
    have hpos : 0 < Module.finrank F K := Module.finrank_pos
    have h1 : Module.finrank F K = 1 := by omega
    rw [h1, pow_one] at hd
    obtain ⟨x, hx⟩ := hFK
    obtain ⟨y, hy⟩ := (Subtype.val_injective.bijective_of_nat_card_le
      (f := fun y : F => (y : K)) hd.le).2 x
    exact hx (hy ▸ y.2)
  have hle : Nat.card F ^ 2 ≤ Nat.card K := by
    rw [hd]
    exact Nat.pow_le_pow_right Nat.card_pos h2
  have hF2 : Nat.card F ≤ 2 ^ f := by
    rw [hK] at hle
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hle
  have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have : (2 ^ f) ^ 2 ≥ 4 * 2 ^ f := by nlinarith
  omega

theorem lower_root_conj_entries {A : Matrix (Fin 3) (Fin 3) K} {c : K} (hA : A.det ≠ 0)
    (h : A * !![1, 0, 0; 0, 1, 0; 1, 0, 1] = c • (!![1, 0, 0; 0, 1, 0; 1, 0, 1] * A)) :
    A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 0 0 = A 2 2 := by
  have e : ∀ i j, (A * !![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) K) i j =
      (c • (!![1, 0, 0; 0, 1, 0; 1, 0, 1] * A) : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e00 e01 e02
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e10 e11 e12
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e20 e21
  simp at e00 e01 e02 e10 e11 e12 e20 e21
  have hc : c = 1 := by
    by_contra hc
    have hc' : (1 : K) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    have zero_of (x : K) (hx : x = c * x) : x = 0 := by
      have : ((1 : K) - c) * x = 0 := by rw [sub_mul, one_mul, ← hx, sub_self]
      exact (mul_eq_zero.mp this).resolve_left hc'
    have h01 := zero_of _ e01
    have h02 := zero_of _ e02
    have h11 := zero_of _ e11
    have h12 := zero_of _ e12
    apply hA
    rw [Matrix.det_fin_three, h01, h02, h11, h12]
    ring
  subst hc
  simp only [one_mul] at e00 e10 e20 e21
  refine ⟨by linear_combination -e21, by linear_combination e00, by linear_combination e10, ?_⟩
  linear_combination -e20

theorem eq_scalar_of_conj {A : Matrix (Fin 3) (Fin 3) K} {c₁ c₂ c₃ a b a' : K}
    (hA : A.det ≠ 0) (ha : a ≠ 0)
    (h1 : A * !![1, 0, 1; 0, 1, 0; 0, 0, 1] = c₁ • (!![1, 0, 1; 0, 1, 0; 0, 0, 1] * A))
    (h2 : A * !![1, 0, 0; 0, 1, 0; 1, 0, 1] = c₂ • (!![1, 0, 0; 0, 1, 0; 1, 0, 1] * A))
    (h3 : A * !![1, a, b; 0, 1, a'; 0, 0, 1] = c₃ • (!![1, a, b; 0, 1, a'; 0, 0, 1] * A)) :
    A = Matrix.scalar (Fin 3) (A 0 0) := by
  obtain ⟨h10, h20, h21, h00⟩ :=
    ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction.central_root_conj_entries hA
      one_ne_zero h1
  obtain ⟨h01, h02, h12, h00'⟩ := lower_root_conj_entries hA h2
  have hA00 : A 0 0 ≠ 0 := by
    intro h0
    apply hA
    rw [Matrix.det_fin_three, h0]
    simp [h10, h20, h21, h01, h02, h12]
  have e : ∀ i j, (A * !![1, a, b; 0, 1, a'; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) i j =
      (c₃ • (!![1, a, b; 0, 1, a'; 0, 0, 1] * A) : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => by rw [h3]
  have e00 := e 0 0
  have e01 := e 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e00 e01
  simp [h10, h20, h21, h01, h02] at e00 e01
  have hc : c₃ = 1 := by
    have : (c₃ - 1) * A 0 0 = 0 := by linear_combination -e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hA00)
  subst hc
  have h11 : A 1 1 = A 0 0 := by
    have : a * (A 1 1 - A 0 0) = 0 := by linear_combination -e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h10, h20, h21, h01, h02, h12, h11]
  linear_combination -h00

end CFSG.Quasithin.Ch3E213M.P4C
