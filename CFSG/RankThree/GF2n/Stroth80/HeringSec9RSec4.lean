module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

section Matrices

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem vecMulVec_mulVec_fix (u v w : Fin 2 → K) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_two]
  ring

theorem eig_of_vecMulVec_eq {v w a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Matrix.vecMulVec v w = Matrix.vecMulVec a b) : ∃ μ : K, v = μ • a := by
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (funext hcon)
  obtain ⟨x, hbx⟩ : ∃ x : Fin 2 → K, b ⬝ᵥ x = 1 :=
    ⟨Pi.single j (b j)⁻¹, by rw [dotProduct_single, mul_inv_cancel₀ hj]⟩
  have h2 : Matrix.vecMulVec v w *ᵥ x = Matrix.vecMulVec a b *ᵥ x := by rw [h]
  rw [vecMulVec_mulVec_fix, vecMulVec_mulVec_fix, hbx, one_smul] at h2
  have hc : w ⬝ᵥ x ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h2
    exact ha h2.symm
  refine ⟨(w ⬝ᵥ x)⁻¹, ?_⟩
  rw [← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem fix_mat_of_pow {A B' : Matrix (Fin 2) (Fin 2) K} {a b : Fin 2 → K} (ha : a ≠ 0)
    (hb : b ≠ 0) {k : ℕ} (hA : A ^ (2 ^ k) = 1)
    (hfix : A * (Matrix.vecMulVec a b * B') = Matrix.vecMulVec a b) :
    A * Matrix.vecMulVec a b = Matrix.vecMulVec a b ∧
      Matrix.vecMulVec a b * B' = Matrix.vecMulVec a b := by
  rw [Matrix.vecMulVec_mul, Matrix.mul_vecMulVec] at hfix
  obtain ⟨μ, hμ⟩ := eig_of_vecMulVec_eq ha hb hfix
  have hpow : ∀ m : ℕ, (A ^ m) *ᵥ a = (μ ^ m) • a := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ m ih =>
      rw [pow_succ' A m, pow_succ μ m, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hμ,
        smul_smul]
  have h1 : (μ ^ (2 ^ k)) • a = a := by
    rw [← hpow (2 ^ k), hA, Matrix.one_mulVec]
  have h2 : μ ^ (2 ^ k) = 1 := by
    have h3 : (μ ^ (2 ^ k) - 1) • a = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right ha)
  have h5 : μ = 1 := by
    have hk2 : (2 ^ k : ℕ) ≠ 0 := by positivity
    have h6 : (μ - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, h2, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff hk2).mp h6)
  have hAa : A *ᵥ a = a := by rw [hμ, h5, one_smul]
  have hw : b ᵥ* B' = b := by
    rw [hAa] at hfix
    exact outerR_injective ha (show outerR a (b ᵥ* B') = outerR a b from hfix)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_vecMulVec, hAa]
  · rw [Matrix.vecMulVec_mul, hw]

theorem coe_pow_eq_one_of_rho {A B : Matrix.SpecialLinearGroup (Fin 2) K} {k : ℕ}
    (h : rho' K (A, B) ^ (2 ^ k) = 1) : (A : Matrix (Fin 2) (Fin 2) K) ^ (2 ^ k) = 1 := by
  have h' : rho' K ((A, B) ^ (2 ^ k)) = rho' K 1 := by
    rw [map_pow, map_one]
    exact h
  have h2 : (A, B) ^ (2 ^ k) = 1 := rho'_injective (K := K) h'
  have h3 : A ^ (2 ^ k) = 1 := congrArg Prod.fst h2
  rw [← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]

theorem fix_of_two_power
    {H₁ H₂ : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : (H₁ = leftF K ∧ H₂ = rightF K) ∨ (H₁ = rightF K ∧ H₂ = leftF K))
    {u₀ : Matrix (Fin 2) (Fin 2) K} (hdet : u₀.det = 0) (hu : u₀ ≠ 0)
    {h₁ h₂ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hh₁ : h₁ ∈ H₁) (hh₂ : h₂ ∈ H₂) {k : ℕ} (hk : (h₁ * h₂) ^ (2 ^ k) = 1)
    (hfix : (h₁ * h₂) u₀ = u₀) : h₁ u₀ = u₀ ∧ h₂ u₀ = u₀ := by
  have hL : ∀ h ∈ leftF K, ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, rho' K (A, 1) = h := by
    intro h hh
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hh
    exact ⟨A, hA⟩
  have hR : ∀ h ∈ rightF K, ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, rho' K (1, B) = h := by
    intro h hh
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hh
    exact ⟨B, hB⟩
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_vecMulVec_of_det_eq_zero hdet hu
  rcases hH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨A, rfl⟩ := hL h₁ hh₁
    obtain ⟨B, rfl⟩ := hR h₂ hh₂
    have hprod : rho' K (A, 1) * rho' K (1, B) = rho' K (A, B) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hprod] at hk
    have hA := coe_pow_eq_one_of_rho hk
    have e : ∀ X : Matrix (Fin 2) (Fin 2) K, (rho' K (A, 1) * rho' K (1, B)) X =
        (A : Matrix (Fin 2) (Fin 2) K) *
          (X * ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
      intro X
      rw [LinearEquiv.mul_apply, rho'_inr_apply, rho'_inl_apply]
    rw [e] at hfix
    obtain ⟨h1, h2⟩ := fix_mat_of_pow ha hb hA hfix
    rw [rho'_inl_apply, rho'_inr_apply]
    exact ⟨h1, h2⟩
  · obtain ⟨B, rfl⟩ := hR h₁ hh₁
    obtain ⟨A, rfl⟩ := hL h₂ hh₂
    have hprod : rho' K (1, B) * rho' K (A, 1) = rho' K (A, B) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
    rw [hprod] at hk
    have hA := coe_pow_eq_one_of_rho hk
    have e : ∀ X : Matrix (Fin 2) (Fin 2) K, (rho' K (1, B) * rho' K (A, 1)) X =
        (A : Matrix (Fin 2) (Fin 2) K) * X *
          ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      intro X
      rw [LinearEquiv.mul_apply, rho'_inl_apply, rho'_inr_apply]
    rw [e, Matrix.mul_assoc] at hfix
    obtain ⟨h1, h2⟩ := fix_mat_of_pow ha hb hA hfix
    rw [rho'_inr_apply, rho'_inl_apply]
    exact ⟨h2, h1⟩

def stab9U (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def stab9T (μ : K) (hμ : μ ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two_of, hμ]⟩

theorem stab9U_mul (b c : K) : stab9U b * stab9U c = stab9U (b + c) := by
  apply Subtype.ext
  change (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, c; 0, 1] = !![1, b + c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem stab9U_zero : stab9U (0 : K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [stab9U, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

theorem stab9U_inv (c : K) : (stab9U c)⁻¹ = stab9U (-c) := by
  rw [inv_eq_iff_mul_eq_one, stab9U_mul, add_neg_cancel, stab9U_zero]

theorem stab9T_conj (μ : K) (hμ : μ ≠ 0) (c : K) :
    stab9T μ hμ * stab9U c * (stab9T μ hμ)⁻¹ = stab9U (μ ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (!![μ, 0; 0, μ⁻¹] : Matrix (Fin 2) (Fin 2) K) * !![1, c; 0, 1] =
    !![1, μ ^ 2 * c; 0, 1] * !![μ, 0; 0, μ⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem stab9U_mulVec (c : K) : (stab9U c : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
  ext i
  fin_cases i <;> simp [stab9U, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem stab9_fix_e1 {X : Matrix.SpecialLinearGroup (Fin 2) K}
    (hX : (X : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0]) :
    X = stab9U ((X : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have h0 := congrFun hX 0
  have h1 := congrFun hX 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hdet := Matrix.SpecialLinearGroup.det_coe X
  rw [Matrix.det_fin_two, h0, h1] at hdet
  have h11 : (X : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simpa using hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [stab9U, h0, h1, h11]

theorem stab9_exists_mu (h4 : 4 ≤ Nat.card K) : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨1, by simp [hcon y hy]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  simp only [Nat.card_fin] at hle
  omega

theorem sl2_stab_data (h4 : 4 ≤ Nat.card K) {w₀ : Fin 2 → K} (hw₀ : w₀ ≠ 0) :
    Nat.card {A : Matrix.SpecialLinearGroup (Fin 2) K //
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀} ≤ Nat.card K ∧
    ∃ (h : Matrix.SpecialLinearGroup (Fin 2) K) (μ : K), μ ^ 2 ≠ 1 ∧
      (h : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = μ • w₀ ∧
      (∀ d₁ d₂ : Matrix.SpecialLinearGroup (Fin 2) K,
        (d₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ →
        (d₂ : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ → d₁ * d₂ = d₂ * d₁) ∧
      ∀ d : Matrix.SpecialLinearGroup (Fin 2) K, (d : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ →
        ∃ d₁ : Matrix.SpecialLinearGroup (Fin 2) K,
          (d₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ ∧ d = d₁⁻¹ * (h * d₁ * h⁻¹) := by
  have he : (![1, 0] : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq he hw₀
  have hginv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ =
      ![1, 0] := by
    rw [← hg, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hconj : ∀ d : Matrix.SpecialLinearGroup (Fin 2) K,
      (d : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ →
        g⁻¹ * d * g = stab9U (((g⁻¹ * d * g : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 1) := by
    intro d hd
    apply stab9_fix_e1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hd, hginv]
  have hform : ∀ d : Matrix.SpecialLinearGroup (Fin 2) K,
      (d : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ → ∃ b : K, d = g * stab9U b * g⁻¹ := by
    intro d hd
    refine ⟨((g⁻¹ * d * g : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
    rw [← hconj d hd]
    group
  have hstab : ∀ c : K, ((g * stab9U c * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := by
    intro c
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hginv, stab9U_mulVec, hg]
  have hcard : Nat.card {A : Matrix.SpecialLinearGroup (Fin 2) K //
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀} ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective
      (fun d : {A : Matrix.SpecialLinearGroup (Fin 2) K //
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀} =>
        ((g⁻¹ * d.1 * g : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 1) ?_
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ hdd
    have hdd' : ((g⁻¹ * d * g : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 1 =
        ((g⁻¹ * d' * g : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 1 := hdd
    have e : g⁻¹ * d * g = g⁻¹ * d' * g := by
      rw [hconj d hd, hconj d' hd', hdd']
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨μ, hμ0, hμ1⟩ := stab9_exists_mu h4
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro h
    apply hμ1
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (μ - 1) * (μ - 1) = 0 := by
      linear_combination h + (1 - μ) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  have hTe : ((stab9T μ hμ0 : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = μ • ![1, 0] := by
    ext i
    fin_cases i <;> simp [stab9T, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hh : ((g * stab9T μ hμ0 * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = μ • w₀ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hginv, hTe, Matrix.mulVec_smul, hg]
  have hcomm : ∀ d₁ d₂ : Matrix.SpecialLinearGroup (Fin 2) K,
      (d₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ →
      (d₂ : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ → d₁ * d₂ = d₂ * d₁ := by
    intro d₁ d₂ h₁ h₂
    obtain ⟨b₁, rfl⟩ := hform d₁ h₁
    obtain ⟨b₂, rfl⟩ := hform d₂ h₂
    calc g * stab9U b₁ * g⁻¹ * (g * stab9U b₂ * g⁻¹)
        = g * (stab9U b₁ * stab9U b₂) * g⁻¹ := by group
      _ = g * stab9U (b₁ + b₂) * g⁻¹ := by rw [stab9U_mul]
      _ = g * stab9U (b₂ + b₁) * g⁻¹ := by rw [add_comm b₁ b₂]
      _ = g * (stab9U b₂ * stab9U b₁) * g⁻¹ := by rw [stab9U_mul]
      _ = g * stab9U b₂ * g⁻¹ * (g * stab9U b₁ * g⁻¹) := by group
  refine ⟨hcard, g * stab9T μ hμ0 * g⁻¹, μ, hμ2, hh, hcomm, ?_⟩
  intro d hd
  obtain ⟨b, rfl⟩ := hform d hd
  have hne : μ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hμ2
  obtain ⟨c, hcb⟩ : ∃ c : K, -c + μ ^ 2 * c = b := by
    refine ⟨b / (μ ^ 2 - 1), ?_⟩
    have h1 : (μ ^ 2 - 1) * (b / (μ ^ 2 - 1)) = b := by
      rw [mul_comm]
      exact div_mul_cancel₀ b hne
    linear_combination h1
  refine ⟨g * stab9U c * g⁻¹, hstab c, ?_⟩
  calc g * stab9U b * g⁻¹ = g * stab9U (-c + μ ^ 2 * c) * g⁻¹ := by rw [hcb]
    _ = g * ((stab9U c)⁻¹ * (stab9T μ hμ0 * stab9U c * (stab9T μ hμ0)⁻¹)) * g⁻¹ := by
        rw [stab9T_conj, stab9U_inv, stab9U_mul]
    _ = (g * stab9U c * g⁻¹)⁻¹ * (g * stab9T μ hμ0 * g⁻¹ * (g * stab9U c * g⁻¹) *
        (g * stab9T μ hμ0 * g⁻¹)⁻¹) := by group

theorem matrix_eq_of_mulVec_eq {A B : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ w : Fin 2 → K, A *ᵥ w = B *ᵥ w) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem ActsNat.exists_hom
    {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    {Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K} (hA : ActsNat H Φ) :
    ∃ ε : ↥H →* Matrix.SpecialLinearGroup (Fin 2) K,
      (∀ (h : ↥H) (w : Fin 2 → K),
        (h : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (Φ w) =
          Φ ((ε h : Matrix (Fin 2) (Fin 2) K) *ᵥ w)) ∧ Function.Surjective ε := by
  classical
  have hex : ∀ h : ↥H, ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ w, (h : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) (Φ w) =
        Φ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := fun h => hA.act h.1 h.2
  choose ε hε using hex
  have huniq : ∀ g g' : Matrix.SpecialLinearGroup (Fin 2) K,
      (∀ w, Φ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = Φ ((g' : Matrix (Fin 2) (Fin 2) K) *ᵥ w)) →
      g = g' := fun g g' h =>
    Subtype.ext (matrix_eq_of_mulVec_eq fun w => hA.inj (h w))
  refine ⟨{ toFun := ε
            map_one' := ?_
            map_mul' := ?_ }, hε, ?_⟩
  · refine huniq _ _ fun w => ?_
    rw [← hε 1 w]
    simp
  · intro a b
    refine huniq _ _ fun w => ?_
    rw [← hε (a * b) w]
    show (((a : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) *
      (b : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)) : _) (Φ w) = _
    rw [LinearEquiv.mul_apply, hε b w, hε a, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec]
  · intro g
    obtain ⟨h, hH, hh⟩ := hA.lift g
    refine ⟨⟨h, hH⟩, huniq _ _ fun w => ?_⟩
    show Φ ((ε ⟨h, hH⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = Φ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    rw [← hε ⟨h, hH⟩ w, hh w]

end Matrices

section Core

theorem sec4_core {hc : Ctx M Q Z B} {X Y : Subgroup G}
    (hQX : Q ≤ X) (hQY : Q ≤ Y) (hYM : Y ≤ M)
    (hcomm : ∀ a ∈ X, ∀ y ∈ Y, ⁅a, y⁆ ∈ Q) (hXYQ : X ⊓ Y = Q)
    (hLXY : LB M Q B ≤ X ⊔ Y) (hLidx : X.relIndex (LB M Q B) = Nat.card Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    (hKq : Nat.card K = Nat.card Z)
    (η : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) K) (w₀ : Fin 2 → K) (hw₀ : w₀ ≠ 0)
    (hηs : Function.Surjective η) (hηk : ∀ y : ↥Y, η y = 1 ↔ (y : G) ∈ Q)
    (hη3 : ∀ y : ↥Y, (∀ b ∈ B, ⁅(y : G), b⁆ ∈ Z) ↔
      (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀)
    (hη4 : ∀ l ∈ LB M Q B, ∀ x ∈ X, ∀ y : ↥Y, x * (y : G) = l →
      (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀)
    (hη5 : ∀ (y : ↥Y) (μ : K), (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = μ • w₀ →
      ∀ b ∈ B, (y : G) * b * (y : G)⁻¹ ∈ (B ⊔ Z : Subgroup G)) :
    Sec4Concl M Q Z B X Y := by
  classical
  set L := LB M Q B with hL
  have hQL : Q ≤ L := sec39_Q_le_LB
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := fun y hy => hZn y (hYM hy)
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := normalizer_of_commutator_le hQX hcomm
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hLX : L ≤ Subgroup.normalizer (X : Set G) :=
    hLXY.trans (sup_le Subgroup.le_normalizer hYX)
  obtain ⟨Y₀, hY₀Y, hY₀⟩ := exists_stabSub (Y := Y) (Z := Z) (B : Set G) hYZ
  have hQY₀ : Q ≤ Y₀ := fun q hq => (hY₀ q).mpr ⟨hQY hq, fun b hb => by
    have hqL : q ∈ L := hQL hq
    exact hc.comm_B_mem_Z hqL hb⟩
  have hY₀η : ∀ y : ↥Y, (y : G) ∈ Y₀ ↔ (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := fun y =>
    ((hY₀ y).trans ⟨fun h => (hη3 y).mp h.2, fun h => ⟨y.2, (hη3 y).mpr h⟩⟩)
  let S : Subgroup G := Y ⊓ (X ⊔ L)
  have hSY : S ≤ Y := inf_le_left
  have hQS : Q ≤ S := le_inf hQY (le_sup_of_le_left hQX)
  have hSmem : ∀ y' ∈ Y, y' ∈ S ↔ ∃ x ∈ X, x * y' ∈ L := by
    intro y' hy'
    constructor
    · intro hS
      have h1 : y' ∈ L ⊔ X := by rw [sup_comm]; exact hS.2
      obtain ⟨l, hl, x, hx, hlx⟩ := exists_mul_of_mem_sup_of_le_normalizer hLX h1
      refine ⟨y' * x⁻¹ * y'⁻¹, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hYX hy') x⁻¹).mp (X.inv_mem hx)
        exact this
      · have e : y' * x⁻¹ * y'⁻¹ * y' = l := by rw [← hlx]; group
        rw [e]
        exact hl
    · rintro ⟨x, hx, hl⟩
      refine ⟨hy', ?_⟩
      have e : y' = x⁻¹ * (x * y') := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (X.inv_mem hx)) (Subgroup.mem_sup_right hl)
  have hSX : Q.relIndex S = Nat.card Z := by
    have h1 : X.relIndex (L ⊔ X) = X.relIndex L := relIndex_sup_right_of_le_normalizer hLX
    have hLXS : L ⊔ X = S ⊔ X := by
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · intro l hl
        obtain ⟨x, hx, y', hy', hxy⟩ := exists_mul_of_mem_sup_of_le_normalizer hXY (hLXY hl)
        have hyS : y' ∈ S := (hSmem y' hy').mpr ⟨x, hx, by rw [hxy]; exact hl⟩
        rw [← hxy]
        exact (S ⊔ X).mul_mem ((le_sup_right : X ≤ S ⊔ X) hx) ((le_sup_left : S ≤ S ⊔ X) hyS)
      · intro y hy
        have h1 : y ∈ X ⊔ L := hy.2
        rw [sup_comm] at h1
        exact h1
    have h2 : X.relIndex (S ⊔ X) = X.relIndex S :=
      relIndex_sup_right_of_le_normalizer (hSY.trans hYX)
    have h3 : X.relIndex S = Q.relIndex S := by
      unfold Subgroup.relIndex
      congr 1
      ext x
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have : (x : G) ∈ X ⊓ Y := ⟨hx, hSY x.2⟩
        rw [hXYQ] at this
        exact this
      · intro hx
        exact hQX hx
    rw [← h3, ← h2, ← hLXS, h1]
    exact hLidx
  have hSY₀ : S ≤ Y₀ := by
    intro y' hy'
    obtain ⟨x, hx, hl⟩ := (hSmem y' (hSY hy')).mp hy'
    exact (hY₀η ⟨y', hSY hy'⟩).mpr (hη4 _ hl x hx ⟨y', hSY hy'⟩ rfl)
  have hY₀le : Q.relIndex Y₀ ≤ Nat.card Z := by
    let f₀ : ↥Y₀ →* Matrix.SpecialLinearGroup (Fin 2) K := η.comp (Subgroup.inclusion hY₀Y)
    have hker : f₀.ker = Q.subgroupOf Y₀ := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hηk ⟨y.1, hY₀Y y.2⟩
    have h1 : Q.relIndex Y₀ = Nat.card f₀.range := by
      rw [← Subgroup.index_ker f₀, hker]
      rfl
    rw [h1, ← hKq]
    obtain ⟨hcard, -⟩ := sl2_stab_data h4 hw₀
    have hfix : ∀ z : f₀.range, (z.1 : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := by
      rintro ⟨z, y, rfl⟩
      exact (hY₀η ⟨y.1, hY₀Y y.2⟩).mp y.2
    refine le_trans (Nat.card_le_card_of_injective
      (fun z : f₀.range => (⟨z.1, hfix z⟩ : {A : Matrix.SpecialLinearGroup (Fin 2) K //
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀})) ?_) hcard
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext h
  have hY₀S : Y₀ ≤ S ∧ Q.relIndex Y₀ = Nat.card Z := by
    have hmul := Subgroup.relIndex_mul_relIndex Q S Y₀ hQS hSY₀
    rw [hSX] at hmul
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hr0 : 0 < S.relIndex Y₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hr : S.relIndex Y₀ = 1 := by
      have h1 : Nat.card Z * S.relIndex Y₀ ≤ Nat.card Z * 1 := by
        rw [hmul, mul_one]
        exact hY₀le
      have := Nat.le_of_mul_le_mul_left h1 hpos
      omega
    refine ⟨Subgroup.relIndex_eq_one.mp hr, ?_⟩
    rw [← hmul, hr, mul_one]
  obtain ⟨-, h, μ, hμ, hhw, habel, hθ⟩ := sl2_stab_data h4 hw₀
  obtain ⟨yh, hyh⟩ := hηs h
  have hyhB : ∀ b ∈ B, (yh : G) * b * (yh : G)⁻¹ ∈ (B ⊔ Z : Subgroup G) :=
    hη5 yh μ (by rw [hyh]; exact hhw)
  have hyhL : conjSubgroup (yh : G) L = L := by
    refine hc.conj_LB_eq_of_le_sup_Z (hYM yh.2) ?_
    intro z hz
    rw [mem_conjSubgroup] at hz
    have := hyhB _ hz
    have e : (yh : G) * ((yh : G)⁻¹ * z * (yh : G)) * (yh : G)⁻¹ = z := by group
    rwa [e] at this
  have hY₀L : Y₀ ≤ L := by
    intro s hs
    have hsY : s ∈ Y := hY₀Y hs
    have hd := (hY₀η ⟨s, hsY⟩).mp hs
    obtain ⟨d₁, hd₁, hdd⟩ := hθ (η ⟨s, hsY⟩) hd
    obtain ⟨s₁, hs₁⟩ := hηs d₁
    have hs₁Y₀ : (s₁ : G) ∈ Y₀ := (hY₀η s₁).mpr (by rw [hs₁]; exact hd₁)
    have hs₁S : (s₁ : G) ∈ S := hY₀S.1 hs₁Y₀
    obtain ⟨x₁, hx₁, hl₁⟩ := (hSmem s₁ s₁.2).mp hs₁S
    set w : G := (s₁ : G)⁻¹ * (yh : G) * (s₁ : G) * (yh : G)⁻¹ with hw
    have hwY : w ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem s₁.2) yh.2) s₁.2) (Y.inv_mem yh.2)
    have hwL : w ∈ L := by
      have h1 : (yh : G) * (x₁ * (s₁ : G)) * (yh : G)⁻¹ ∈ L := by
        have : (yh : G) * (x₁ * (s₁ : G)) * (yh : G)⁻¹ ∈ conjSubgroup (yh : G) L := by
          rw [mem_conjSubgroup]
          have e : (yh : G)⁻¹ * ((yh : G) * (x₁ * (s₁ : G)) * (yh : G)⁻¹) * (yh : G) =
              x₁ * (s₁ : G) := by group
          rw [e]
          exact hl₁
        rwa [hyhL] at this
      have hq : x₁⁻¹ * (yh : G) * x₁ * (yh : G)⁻¹ ∈ Q := by
        have := hcomm x₁⁻¹ (X.inv_mem hx₁) (yh : G) yh.2
        simpa [commutatorElement_def] using this
      have hq' : (s₁ : G)⁻¹ * (x₁⁻¹ * (yh : G) * x₁ * (yh : G)⁻¹) * (s₁ : G) ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hQn (hYM (Y.inv_mem s₁.2))) _).mp hq
        simpa using this
      have e : w = ((s₁ : G)⁻¹ * (x₁⁻¹ * (yh : G) * x₁ * (yh : G)⁻¹) * (s₁ : G))⁻¹ *
          ((x₁ * (s₁ : G))⁻¹ * ((yh : G) * (x₁ * (s₁ : G)) * (yh : G)⁻¹)) := by
        rw [hw]; group
      rw [e]
      exact L.mul_mem (L.inv_mem (hQL hq')) (L.mul_mem (L.inv_mem hl₁) h1)
    have hηw : η ⟨w, hwY⟩ = η ⟨s, hsY⟩ := by
      have e : (⟨w, hwY⟩ : ↥Y) = s₁⁻¹ * yh * s₁ * yh⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hs₁, hyh, hdd]
      group
    have hone : η ((⟨w, hwY⟩ : ↥Y)⁻¹ * ⟨s, hsY⟩) = 1 := by
      rw [map_mul, map_inv, hηw]
      group
    have hwsQ : w⁻¹ * s ∈ Q := (hηk _).mp hone
    have e : s = w * (w⁻¹ * s) := by group
    rw [e]
    exact L.mul_mem hwL (hQL hwsQ)
  have hLY : L ⊓ Y = Y₀ := le_antisymm
    (fun y hy => (hY₀ y).mpr ⟨hy.2, fun b hb => hc.comm_B_mem_Z hy.1 hb⟩)
    (fun y hy => ⟨hY₀L hy, hY₀Y hy⟩)
  refine ⟨fun y => ?_, ?_, ?_⟩
  · rw [hLY]
    exact hY₀ y
  · rw [hLY]
    exact hY₀S.2
  · refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro l hl
    obtain ⟨x, hx, y', hy', hxy⟩ := exists_mul_of_mem_sup_of_le_normalizer hXY (hLXY hl)
    have hy'S : y' ∈ S := (hSmem y' hy').mpr ⟨x, hx, by rw [hxy]; exact hl⟩
    have hy'L : y' ∈ L ⊓ Y := by
      rw [hLY]
      exact hSY₀ hy'S
    have hxL : x ∈ L ⊓ X := by
      refine ⟨?_, hx⟩
      have e : x = l * y'⁻¹ := by rw [← hxy]; group
      rw [e]
      exact L.mul_mem hl (L.inv_mem hy'L.1)
    rw [← hxy]
    exact (((L ⊓ X) ⊔ (L ⊓ Y)) : Subgroup G).mul_mem (Subgroup.mem_sup_left hxL)
      (Subgroup.mem_sup_right hy'L)

end Core

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_factor {H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)}
    (hH : H = leftF K ∨ H = rightF K) :
    Nat.card ↥H = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    (card_statedSL 2 K).symm.trans (card_statedSL_two K)
  rcases hH with hH' | hH' <;> rw [hH']
  · have hinj : Function.Injective
        ((rho' K).comp (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K) _)) := by
      intro a b hab
      have h2 : rho' K (MonoidHom.inl _ _ a) = rho' K (MonoidHom.inl _ _ b) := hab
      exact congrArg Prod.fst (rho'_injective h2)
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcardSL
  · have hinj : Function.Injective
        ((rho' K).comp (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K) _)) := by
      intro a b hab
      have h2 : rho' K (MonoidHom.inr _ _ a) = rho' K (MonoidHom.inr _ _ b) := hab
      exact congrArg Prod.snd (rho'_injective h2)
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcardSL

end Model

end HS9

open HS9


theorem sec4_model (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      4 ≤ Nat.card K ∧ Nat.card K = Nat.card Z ∧
      ∃ (η : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) K) (w₀ : Fin 2 → K), w₀ ≠ 0 ∧
        Function.Surjective η ∧ (∀ y : ↥Y, η y = 1 ↔ (y : G) ∈ Q) ∧
        (∀ y : ↥Y, (∀ b ∈ B, ⁅(y : G), b⁆ ∈ Z) ↔
          (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀) ∧
        (∀ l ∈ LB M Q B, ∀ x ∈ X, ∀ y : ↥Y, x * (y : G) = l →
          (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀) ∧
        (∀ (y : ↥Y) (μ : K), (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = μ • w₀ →
          ∀ b ∈ B, (y : G) * b * (y : G)⁻¹ ∈ (B ⊔ Z : Subgroup G)) := by
  classical
  have hhead := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨u, hQu, hu0, hBiff, -, -⟩ := hc.omega_points_flag h34 hs5 hnotQB hK
    (ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)) hQ h3
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
  have hdet : (toMat K u).det = 0 := by
    rw [det_toMat]
    exact (congrFun (coe_quadPlus 2 K) u).symm.trans hQu
  have hu0' : toMat K u ≠ 0 := fun h => hu0 ((toMat K).injective (by rw [h, map_zero]))
  have hq4Z : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  obtain ⟨hYQnorm, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := HS9.isSLModel_two_data hq4Z hq2 hYmod
  have hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := HS9.normalizer_of_commutator_le hQX hcomm
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRX : Rt M (LB M Q B) t ≤ Subgroup.normalizer (X : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le Subgroup.le_normalizer hYX
  have hRY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ x ∈ X, ∃ y ∈ Y, x * y = r := by
    intro r hr
    have hr' : r ∈ (↑(X ⊔ Y) : Set G) := by rw [hXY]; exact hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY'] at hr'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hr'
    exact ⟨x, hx, y, hy, hxy⟩
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hφ''1 : ∀ s : ↥(Rt M (LB M Q B) t), φ'' s = 1 ↔ (s : G) ∈ hc.CN t := by
    intro s
    show Ψ K (φ s) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hrange : φ''.range = (rho' K).range := by
    have h1 : φ''.range = φ.range.map (Ψ K).toMonoidHom := MonoidHom.range_comp _ _
    rw [h1, hφ, map_statedOmega, commutator_eq_range hq4]
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    (card_statedSL 2 K).symm.trans (card_statedSL_two K)
  have hcardRange : Nat.card (rho' K).range =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (rho'_injective (K := K))).toEquiv,
      Nat.card_prod, hcardSL]
  haveI hΛfin : Finite (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    Finite.of_injective (fun f => (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
      (fun f g h => LinearEquiv.ext (congrFun h))
  let HY := (Y.subgroupOf (Rt M (LB M Q B) t)).map φ''
  let HX := (X.subgroupOf (Rt M (LB M Q B) t)).map φ''
  have hle_range : ∀ H' : Subgroup ↥(Rt M (LB M Q B) t), H'.map φ'' ≤ (rho' K).range :=
    fun H' => hrange ▸ Subgroup.map_le_range φ'' H'
  have hnY : ∀ g ∈ (rho' K).range, ∀ h ∈ HY, g * h * g⁻¹ ∈ HY := by
    intro g hg h hh
    rw [← hrange] at hg
    obtain ⟨r, rfl⟩ := hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨r * y * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ((r : G) * (y : G) * (r : G)⁻¹) ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp (hRY r.2) y).mp hy
  have hnX : ∀ g ∈ (rho' K).range, ∀ h ∈ HX, g * h * g⁻¹ ∈ HX := by
    intro g hg h hh
    rw [← hrange] at hg
    obtain ⟨r, rfl⟩ := hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨r * y * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ((r : G) * (y : G) * (r : G)⁻¹) ∈ X
    exact (Subgroup.mem_normalizer_iff.mp (hRX r.2) y).mp hy
  have hcXY : ∀ x ∈ HX, ∀ y ∈ HY, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hq : ((a * b * a⁻¹ * b⁻¹ : ↥(Rt M (LB M Q B) t)) : G) ∈ hc.CN t := by
      have h1 : ((a * b * a⁻¹ * b⁻¹ : ↥(Rt M (LB M Q B) t)) : G) = ⁅(a : G), (b : G)⁆ := by
        simp [commutatorElement_def]
      rw [h1]
      exact hc.Q_le_CN ht (hcomm a ha b hb)
    have h2 : φ'' (a * b * a⁻¹ * b⁻¹) = 1 := (hφ''1 _).mpr hq
    simp only [map_mul, map_inv] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rwa [commutatorElement_def])
  have hHYne : HY ≠ ⊥ := by
    intro hbot
    have hYN : Y ≤ hc.CN t := by
      intro y hy
      have hyR : y ∈ Rt M (LB M Q B) t := hYR hy
      have h1 : φ'' ⟨y, hyR⟩ = 1 := by
        have hmem : φ'' ⟨y, hyR⟩ ∈ HY := Subgroup.mem_map.mpr ⟨⟨y, hyR⟩, hy, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact (hφ''1 _).mp h1
    have hYQ : Y ≤ Q := by
      intro y hy
      rw [← hXYQ]
      exact ⟨hhead (hYN hy), hy⟩
    have h1 : Q.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr hYQ
    rw [hQY_idx] at h1
    have := Nat.eq_one_of_mul_eq_one_right h1
    omega
  have hcardHY : Nat.card HY ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
    let f : ↥Y →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
      φ''.comp (Subgroup.inclusion hYR)
    have hrangef : f.range = HY := by
      ext h
      constructor
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map.mpr ⟨⟨y, hYR y.2⟩, y.2, rfl⟩
      · intro hh
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hh
        exact ⟨⟨s, hs⟩, rfl⟩
    have hQker : Q.subgroupOf Y ≤ f.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      show φ'' ⟨(y : G), hYR y.2⟩ = 1
      exact (hφ''1 _).mpr (hc.Q_le_CN ht (Subgroup.mem_subgroupOf.mp hy))
    rw [← hrangef, ← Subgroup.index_ker f]
    have hdvd := Subgroup.index_dvd_of_le hQker
    have hpos : 0 < (Q.subgroupOf Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    calc f.ker.index ≤ (Q.subgroupOf Y).index := Nat.le_of_dvd hpos hdvd
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := by rw [hK]; exact hQY_idx
  have hHXne : HX ≠ ⊥ := by
    intro hbot
    have hle : (rho' K).range ≤ HY := by
      rw [← hrange]
      rintro _ ⟨r, rfl⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := hdec r.1 r.2
      have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
      have hyR : y ∈ Rt M (LB M Q B) t := hYR hy
      have hr : r = ⟨x, hxR⟩ * ⟨y, hyR⟩ := Subtype.ext hxy.symm
      have hx1 : φ'' ⟨x, hxR⟩ = 1 := by
        have hmem : φ'' ⟨x, hxR⟩ ∈ HX := Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hx, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      rw [hr, map_mul, hx1, one_mul]
      exact Subgroup.mem_map.mpr ⟨⟨y, hyR⟩, hy, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardRange] at h1
    have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
    have hpos : 2 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
      have : 1 ≤ Nat.card K ^ 2 - 1 := by omega
      nlinarith
    nlinarith [hcardHY]
  have hcls := eq_leftF_or_rightF hq4 hnY hnX (hle_range _) (hle_range _) hHYne hHXne
    (fun x hx y hy => (hcXY y hy x hx).symm)
  have hfac : HY = leftF K ∨ HY = rightF K := by
    rcases hcls with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hpair : (HX = leftF K ∧ HY = rightF K) ∨ (HX = rightF K ∧ HY = leftF K) := by
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  obtain ⟨Φ, w₀, hA, hw₀, hu⟩ := natural_module_data hfac hdet hu0'
  obtain ⟨ε, hε, hεs⟩ := hA.exists_hom
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hsc := secVec_comm φ ψ hψ hnorm
  let f : ↥Y →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    φ''.comp (Subgroup.inclusion hYR)
  have hfmem : ∀ y : ↥Y, f y ∈ HY := fun y => Subgroup.mem_map.mpr ⟨⟨y, hYR y.2⟩, y.2, rfl⟩
  let g : ↥Y →* ↥HY := f.codRestrict HY hfmem
  let η : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) K := ε.comp g
  have hcardHYeq : Nat.card ↥HY = Nat.card K * (Nat.card K ^ 2 - 1) := card_factor hfac
  have hεinj : Function.Injective ε :=
    (hεs.bijective_of_nat_card_le (le_of_eq (by rw [hcardHYeq, hcardSL]))).1
  have hfrange : f.range = HY := by
    ext h
    constructor
    · rintro ⟨y, rfl⟩
      exact hfmem y
    · intro hh
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hh
      exact ⟨⟨s, hs⟩, rfl⟩
  have hQker : Q.subgroupOf Y ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    show φ'' ⟨(y : G), hYR y.2⟩ = 1
    exact (hφ''1 _).mpr (hc.Q_le_CN ht (Subgroup.mem_subgroupOf.mp hy))
  have hfker : f.ker = Q.subgroupOf Y := by
    refine le_antisymm ?_ hQker
    have hidx : f.ker.index = (Q.subgroupOf Y).index := by
      rw [Subgroup.index_ker f, hfrange, hcardHYeq]
      show _ = Q.relIndex Y
      rw [hQY_idx, hK]
    have h1 := Subgroup.relIndex_mul_index hQker
    rw [hidx] at h1
    have hpos : 0 < (Q.subgroupOf Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h2 : (Q.subgroupOf Y).relIndex f.ker = 1 := by
      have : (Q.subgroupOf Y).relIndex f.ker * (Q.subgroupOf Y).index =
          1 * (Q.subgroupOf Y).index := by rw [h1, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact Subgroup.relIndex_eq_one.mp h2
  have hηk : ∀ y : ↥Y, η y = 1 ↔ (y : G) ∈ Q := by
    intro y
    constructor
    · intro h
      have h1 : g y = 1 := hεinj (by rw [map_one]; exact h)
      have h2 : f y = 1 := congrArg Subtype.val h1
      have h3 : y ∈ f.ker := h2
      rw [hfker] at h3
      exact Subgroup.mem_subgroupOf.mp h3
    · intro h
      have h3 : y ∈ Q.subgroupOf Y := Subgroup.mem_subgroupOf.mpr h
      rw [← hfker] at h3
      have h2 : f y = 1 := h3
      have h1 : g y = 1 := Subtype.ext h2
      show ε (g y) = 1
      rw [h1, map_one]
  have hgs : Function.Surjective g := by
    intro h
    obtain ⟨s, hsY, hs⟩ := Subgroup.mem_map.mp h.2
    exact ⟨⟨s.1, hsY⟩, Subtype.ext hs⟩
  have hηs : Function.Surjective η := hεs.comp hgs
  have hΨ : ∀ (A : GL (Fin 2 ⊕ Fin 2) K) (c : K),
      Ψ K A (toMat K u) = c • toMat K u ↔
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = c • u := by
    intro A c
    rw [Ψ_apply, LinearEquiv.symm_apply_apply, ← map_smul]
    exact (toMat K).injective.eq_iff
  have hηact : ∀ (y : ↥Y) (c : K), (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = c • w₀ ↔
      (φ ⟨(y : G), hYR y.2⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = c • u := by
    intro y c
    have h1 : Ψ K (φ ⟨(y : G), hYR y.2⟩) (Φ w₀) =
        Φ ((η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀) := hε (g y) w₀
    constructor
    · intro h
      refine (hΨ _ c).mp ?_
      rw [hu, h1, h, map_smul]
    · intro h
      have h3 := (hΨ _ c).mpr h
      rw [hu, h1, ← map_smul] at h3
      exact hA.inj h3
  have hη3 : ∀ y : ↥Y, (∀ b ∈ B, ⁅(y : G), b⁆ ∈ Z) ↔
      (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := by
    intro y
    have h0 := hηact y 1
    rw [one_smul, one_smul] at h0
    rw [h0]
    set s : ↥(Rt M (LB M Q B) t) := ⟨(y : G), hYR y.2⟩ with hsdef
    constructor
    · intro h
      obtain ⟨b₀, hb₀B, hb₀v⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
      have h1 := (secVec_eq_zero_iff ψ
        ⟨⁅(s : G), (b₀ : G)⁆, comm_mem_of_le_normalizer hnorm s b₀⟩).mpr (h _ hb₀B)
      rw [hsc s b₀, hb₀v, sub_eq_zero] at h1
      exact h1
    · intro hφu b hb
      have hbV : b ∈ Vt M (LB M Q B) B Z t := hBV hb
      obtain ⟨c, hc'⟩ := (hBiff (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
      refine (secVec_eq_zero_iff ψ
        ⟨⁅(s : G), b⁆, comm_mem_of_le_normalizer hnorm s ⟨b, hbV⟩⟩).mp ?_
      rw [hsc s ⟨b, hbV⟩, hc', Matrix.mulVec_smul, hφu, sub_self]
  have hη4 : ∀ l ∈ LB M Q B, ∀ x ∈ X, ∀ y : ↥Y, x * (y : G) = l →
      (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = w₀ := by
    intro l hl x hx y hxy
    have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht hl
    have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
    have hyR : (y : G) ∈ Rt M (LB M Q B) t := hYR y.2
    have hφl : (φ ⟨l, hlR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u = u := by
      obtain ⟨b₀, hb₀B, hb₀v⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
      have h1 := (secVec_eq_zero_iff ψ
        ⟨⁅l, (b₀ : G)⁆, comm_mem_of_le_normalizer hnorm ⟨l, hlR⟩ b₀⟩).mpr
          (hc.comm_B_mem_Z hl hb₀B)
      rw [hsc ⟨l, hlR⟩ b₀, hb₀v, sub_eq_zero] at h1
      exact h1
    have hL2 := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
    obtain ⟨k, hk⟩ := hL2 ⟨l, hl⟩
    have hlxy : (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) = ⟨x, hxR⟩ * ⟨(y : G), hyR⟩ :=
      Subtype.ext hxy.symm
    have hφ''l : φ'' ⟨l, hlR⟩ = φ'' ⟨x, hxR⟩ * φ'' ⟨(y : G), hyR⟩ := by rw [hlxy, map_mul]
    have hpow : (φ'' ⟨x, hxR⟩ * φ'' ⟨(y : G), hyR⟩) ^ (2 ^ k) = 1 := by
      rw [← hφ''l, ← map_pow]
      have : (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) ^ (2 ^ k) = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      rw [this, map_one]
    have hfixl : (φ'' ⟨x, hxR⟩ * φ'' ⟨(y : G), hyR⟩) (toMat K u) = toMat K u := by
      rw [← hφ''l]
      have := (hΨ (φ ⟨l, hlR⟩) 1).mpr (by rw [one_smul]; exact hφl)
      rw [one_smul] at this
      exact this
    have hh₁ : φ'' ⟨x, hxR⟩ ∈ HX := Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hx, rfl⟩
    have hh₂ : φ'' ⟨(y : G), hyR⟩ ∈ HY := Subgroup.mem_map.mpr ⟨⟨(y : G), hyR⟩, y.2, rfl⟩
    obtain ⟨-, h2⟩ := fix_of_two_power hpair hdet hu0' hh₁ hh₂ hpow hfixl
    have h3 := (hΨ (φ ⟨(y : G), hyR⟩) 1).mp (by rw [one_smul]; exact h2)
    have h4 := (hηact y 1).mpr h3
    rwa [one_smul] at h4
  have hη5 : ∀ (y : ↥Y) (μ : K), (η y : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ = μ • w₀ →
      ∀ b ∈ B, (y : G) * b * (y : G)⁻¹ ∈ (B ⊔ Z : Subgroup G) := by
    intro y μ hyμ b hb
    have hφμ := (hηact y μ).mp hyμ
    set s : ↥(Rt M (LB M Q B) t) := ⟨(y : G), hYR y.2⟩ with hsdef
    have hbV : b ∈ Vt M (LB M Q B) B Z t := hBV hb
    obtain ⟨c, hc'⟩ := (hBiff (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
    have hwV : (y : G) * b * (y : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hnorm s.2) b).mp hbV
    have hsv : secVec ψ ⟨(y : G) * b * (y : G)⁻¹, hwV⟩ = (c * μ) • u := by
      have h1 := hψ s ⟨b, hbV⟩ ⟨(y : G) * b * (y : G)⁻¹, hwV⟩ rfl
      show Multiplicative.toAdd (ψ (QuotientGroup.mk _)) = _
      rw [h1]
      show (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ ⟨b, hbV⟩ = _
      rw [hc', Matrix.mulVec_smul, hφμ, smul_smul]
    obtain ⟨b', hb'B, hb'v⟩ := (hBiff ((c * μ) • u)).mpr ⟨c * μ, rfl⟩
    have hz : (y : G) * b * (y : G)⁻¹ * (b' : G)⁻¹ ∈ Z :=
      (secVec_eq_iff ψ ⟨(y : G) * b * (y : G)⁻¹, hwV⟩ b').mp (hsv.trans hb'v.symm)
    have e : (y : G) * b * (y : G)⁻¹ =
        ((y : G) * b * (y : G)⁻¹ * (b' : G)⁻¹) * (b' : G) := by group
    rw [sup_comm, e]
    exact Subgroup.mul_mem_sup hz hb'B
  exact ⟨K, fK, finK, inferInstance, hq4, hK, η, w₀, hw₀, hηs, hηk, hη3, hη4, hη5⟩

theorem sec4_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) : Sec4Statement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit
  obtain ⟨K, fK, finK, chK, h4, hKq, η, w₀, hw₀, hηs, hηk, hη3, hη4, hη5⟩ :=
    sec4_model h34 h311a hs hsplit
  have hhead := sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  have hLXY : LB M Q B ≤ X ⊔ Y := (le_Rt (LB M Q B) ht).trans hXY.ge
  have hLidx : X.relIndex (LB M Q B) = Nat.card Z := by
    have hLN_idx : (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
      rw [Subgroup.inf_relIndex_left]
      exact HS9.relIndex_LB_CN h34 hs
    have hmul := Subgroup.relIndex_mul_relIndex (LB M Q B ⊓ hc.CN t) (LB M Q B ⊓ X) (LB M Q B)
      (inf_le_inf_left _ hhead.1) inf_le_left
    have hEq : (LB M Q B ⊓ hc.CN t) ⊓ (LB M Q B ⊓ X) = hc.CN t ⊓ (LB M Q B ⊓ X) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2⟩⟩
    have hA : (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B ⊓ X) =
        (hc.CN t).relIndex (LB M Q B ⊓ X) := by
      rw [← Subgroup.inf_relIndex_right (LB M Q B ⊓ hc.CN t), ← Subgroup.inf_relIndex_right
        (hc.CN t), hEq]
    have hB : (LB M Q B ⊓ X).relIndex (LB M Q B) = X.relIndex (LB M Q B) := by
      rw [Subgroup.inf_relIndex_left]
    have hq0 : 0 < Nat.card Z := Nat.card_pos
    rw [hhead.2, hLN_idx, hB] at hmul
    exact Nat.eq_of_mul_eq_mul_left hq0 (by rw [hmul]; ring)
  exact sec4_core (hc := hc) hQX hQY hYM hcomm hXYQ hLXY hLidx h4 hKq η w₀ hw₀ hηs hηk hη3 hη4
    hη5

end CFSG.RankThree.GF2n.Stroth80
