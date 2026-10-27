module

public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix Polynomial

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

theorem frob_add (x y : K) : (x + y) ^ 2 ^ a = x ^ 2 ^ a + y ^ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow x y 2 a

omit [CharP K 2] in
theorem frob_mul (x y : K) : (x * y) ^ 2 ^ a = x ^ 2 ^ a * y ^ 2 ^ a := mul_pow x y _

variable [Finite K]

omit [CharP K 2] in
theorem frob_frob (hK : Nat.card K = 2 ^ (2 * a)) (x : K) : (x ^ 2 ^ a) ^ 2 ^ a = x := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← pow_add, show a + a = 2 * a by ring, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem exists_frob_ne (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a)) :
    ∃ t : K, t + t ^ 2 ^ a ≠ 0 := by
  by_contra h
  push Not at h
  have := Fintype.ofFinite K
  have hq : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hsub : (Finset.univ : Finset K).val ⊆ (X ^ 2 ^ a - X : K[X]).roots := by
    intro t _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
    calc t ^ 2 ^ a - t = t + t ^ 2 ^ a := by rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
      _ = 0 := h t
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hK] at hcard
  have : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem exists_trace_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a)) :
    ∃ t : K, t + t ^ 2 ^ a = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_frob_ne a ha hK
  set τ := t₀ + t₀ ^ 2 ^ a with hτ
  have hστ : τ ^ 2 ^ a = τ := by
    rw [hτ, frob_add, frob_frob a hK, add_comm]
  refine ⟨t₀ * τ⁻¹, ?_⟩
  rw [frob_mul, inv_pow, hστ, ← add_mul, ← hτ, mul_inv_cancel₀ ht₀]

@[expose] def tw (M X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  M * X * (frobPow a M)ᵀ

abbrev IsHerm (X : Matrix (Fin 2) (Fin 2) K) : Prop := (frobPow a X)ᵀ = X

omit [CharP K 2] [Finite K] in
theorem isHerm_iff (X : Matrix (Fin 2) (Fin 2) K) :
    IsHerm a X ↔ X 0 0 ^ 2 ^ a = X 0 0 ∧ X 1 1 ^ 2 ^ a = X 1 1 ∧ X 0 1 ^ 2 ^ a = X 1 0 ∧
      X 1 0 ^ 2 ^ a = X 0 1 := by
  constructor
  · intro h
    have e : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => congrFun (congrFun h i) j
    exact ⟨e 0 0, e 1 1, e 1 0, e 0 1⟩
  · rintro ⟨h00, h11, h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow, h00, h11, h01, h10]

omit [Finite K] in
theorem isHerm_add {X Y : Matrix (Fin 2) (Fin 2) K} (hX : IsHerm a X) (hY : IsHerm a Y) :
    IsHerm a (X + Y) := by
  rw [isHerm_iff] at hX hY ⊢
  simp only [Matrix.add_apply, frob_add]
  exact ⟨by rw [hX.1, hY.1], by rw [hX.2.1, hY.2.1], by rw [hX.2.2.1, hY.2.2.1],
    by rw [hX.2.2.2, hY.2.2.2]⟩

theorem isHerm_tw (hK : Nat.card K = 2 ^ (2 * a)) (M : Matrix (Fin 2) (Fin 2) K)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : IsHerm a X) : IsHerm a (tw a M X) := by
  have hmap : ∀ A B : Matrix (Fin 2) (Fin 2) K, frobPow a (A * B) = frobPow a A * frobPow a B :=
    fun A B => by
      ext i j
      simp only [frobPow, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, frob_add,
        frob_mul]
  have htr : ∀ A : Matrix (Fin 2) (Fin 2) K, frobPow a Aᵀ = (frobPow a A)ᵀ := fun A => rfl
  have hff : frobPow a (frobPow a M) = M := by
    ext i j
    exact frob_frob a hK _
  unfold IsHerm at hX ⊢
  unfold tw
  rw [hmap, hmap, htr, hff, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hX, Matrix.mul_assoc]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
