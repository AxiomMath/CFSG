module

public import CFSG.CGT.Timmesfeld75.ListWCLinPair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix CFSG.CGT.Timmesfeld75

theorem exists_vecMulVec_of_forall_vecMul_eq_zero {K : Type*} [Field K] {m : ℕ}
    {c : Fin m → K} (hc : c ≠ 0) (N : Matrix (Fin m) (Fin m) K)
    (h : ∀ a : Fin m → K, a ⬝ᵥ c = 0 → a ᵥ* N = 0) :
    ∃ b : Fin m → K, N = Matrix.vecMulVec c b := by
  have hcol : ∀ j : Fin m, (fun i => N i j) ∈ Submodule.span K {c} := by
    intro j
    by_contra hnot
    obtain ⟨χ, h0, h1⟩ := CFSG.CGT.Timmesfeld75.exists_dot_of_notMem
      (S := Submodule.span K {c}) (d := fun i => N i j) hnot
    have hχ : χ ᵥ* N = 0 := h χ (h0 c (Submodule.mem_span_singleton_self c))
    have hj : χ ⬝ᵥ (fun i => N i j) = 0 := congrFun hχ j
    exact one_ne_zero (h1.symm.trans hj)
  have hcol' : ∀ j : Fin m, ∃ β : K, β • c = fun i => N i j := fun j =>
    Submodule.mem_span_singleton.1 (hcol j)
  choose b hb using hcol'
  refine ⟨b, ?_⟩
  ext i j
  have hij : b j * c i = N i j := by
    simpa using congrFun (hb j) i
  rw [Matrix.vecMulVec_apply, ← hij]
  ring

theorem exists_vecMulVec_of_forall_mulVec_eq_zero {K : Type*} [Field K] {m : ℕ}
    {a : Fin m → K} (ha : a ≠ 0) (N : Matrix (Fin m) (Fin m) K)
    (h : ∀ v : Fin m → K, a ⬝ᵥ v = 0 → N *ᵥ v = 0) :
    ∃ w : Fin m → K, N = Matrix.vecMulVec w a := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 ha
  have hk' : a k ≠ 0 := by simpa using hk
  have hae : a ⬝ᵥ Pi.single k (1 : K) = a k := by
    rw [dotProduct_single, mul_one]
  have key : ∀ u : Fin m → K,
      N *ᵥ u = (a ⬝ᵥ u) • ((a k)⁻¹ • (N *ᵥ Pi.single k (1 : K))) := by
    intro u
    have hv : a ⬝ᵥ (u - ((a ⬝ᵥ u) * (a k)⁻¹) • Pi.single k (1 : K)) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hae, smul_eq_mul, mul_assoc,
        inv_mul_cancel₀ hk', mul_one, sub_self]
    have h0 := h _ hv
    rw [mulVec_sub, mulVec_smul, sub_eq_zero] at h0
    rw [h0, mul_smul]
  refine ⟨(a k)⁻¹ • (N *ᵥ Pi.single k (1 : K)), ?_⟩
  ext i j
  have hN : (N *ᵥ Pi.single j (1 : K)) i = N i j := by
    rw [mulVec_single_one]
    rfl
  have hj := congrFun (key (Pi.single j (1 : K))) i
  simp only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul, hN] at hj
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [hj]
  ring

variable {K : Type*} [Field K] {m : ℕ}

theorem exists_ne_zero_dotProduct_eq_zero_of_two_le (hm : 2 ≤ m) {c : Fin m → K} (hc : c ≠ 0) :
    ∃ a : Fin m → K, a ≠ 0 ∧ a ⬝ᵥ c = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
  have hj' : c j ≠ 0 := by simpa using hj
  obtain ⟨i, hij⟩ : ∃ i : Fin m, i ≠ j := by
    by_contra hall
    push Not at hall
    have h0 : (⟨0, by omega⟩ : Fin m) = j := hall _
    have h1 : (⟨1, by omega⟩ : Fin m) = j := hall _
    have := h0.trans h1.symm
    simp [Fin.ext_iff] at this
  refine ⟨Pi.single i (c j) - Pi.single j (c i), fun h => ?_, ?_⟩
  · have := congrFun h i
    simp [Pi.single_apply, hij] at this
    exact hj' this
  · rw [sub_dotProduct, single_dotProduct, single_dotProduct]
    ring

theorem eq_smul_one_add_vecMulVec_of_commute_center (hm : 2 ≤ m) {c : Fin m → K} (hc : c ≠ 0)
    {X : Matrix (Fin m) (Fin m) K}
    (h : ∀ a : Fin m → K, a ⬝ᵥ c = 0 →
      X * (1 + vecMulVec c a) = (1 + vecMulVec c a) * X) :
    ∃ (μ : K) (b : Fin m → K), b ⬝ᵥ c = 0 ∧ X = μ • (1 : Matrix (Fin m) (Fin m) K) +
      vecMulVec c b := by
  have h1 : ∀ a : Fin m → K, a ⬝ᵥ c = 0 →
      vecMulVec (X *ᵥ c) a = vecMulVec c (a ᵥ* X) := by
    intro a ha
    have := h a ha
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at this
    have := add_left_cancel this
    rwa [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at this
  obtain ⟨a₀, ha₀, ha₀c⟩ := exists_ne_zero_dotProduct_eq_zero_of_two_le hm hc
  obtain ⟨μ₀, hμ₀, -⟩ := exists_smul_of_vecMulVec_eq (h1 a₀ ha₀c) hc ha₀
  have h2 : ∀ a : Fin m → K, a ⬝ᵥ c = 0 → a ᵥ* X = μ₀ • a := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, zero_vecMul, smul_zero]
    obtain ⟨μ, hμ, hμ'⟩ := exists_smul_of_vecMulVec_eq (h1 a ha) hc ha0
    have : μ = μ₀ := by
      have h3 : μ • c = μ₀ • c := hμ.symm.trans hμ₀
      by_contra hne
      apply hc
      have h4 : (μ - μ₀) • c = 0 := by rw [sub_smul, h3, sub_self]
      exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hne)
    rw [hμ', this]
  have h3 : ∀ a : Fin m → K, a ⬝ᵥ c = 0 → a ᵥ* (X - μ₀ • (1 : Matrix (Fin m) (Fin m) K)) = 0 := by
    intro a ha
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, h2 a ha, sub_self]
  obtain ⟨b, hb⟩ := exists_vecMulVec_of_forall_vecMul_eq_zero hc _ h3
  refine ⟨μ₀, b, ?_, by rw [← hb]; abel⟩
  have h4 : X *ᵥ c = μ₀ • c := hμ₀
  have h5 : X = μ₀ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c b := by rw [← hb]; abel
  rw [h5, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    at h4
  rw [op_smul_eq_smul] at h4
  have h6 : (b ⬝ᵥ c) • c = 0 := add_eq_left.1 h4
  exact (smul_eq_zero.1 h6).resolve_right hc

theorem eq_smul_one_add_vecMulVec_of_commute_axis (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0)
    {X : Matrix (Fin m) (Fin m) K}
    (h : ∀ v : Fin m → K, a ⬝ᵥ v = 0 →
      X * (1 + vecMulVec v a) = (1 + vecMulVec v a) * X) :
    ∃ (μ : K) (w : Fin m → K), a ⬝ᵥ w = 0 ∧ X = μ • (1 : Matrix (Fin m) (Fin m) K) +
      vecMulVec w a := by
  have h1 : ∀ v : Fin m → K, a ⬝ᵥ v = 0 →
      vecMulVec (X *ᵥ v) a = vecMulVec v (a ᵥ* X) := by
    intro v hv
    have := h v hv
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at this
    have := add_left_cancel this
    rwa [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at this
  obtain ⟨v₀, hv₀, hv₀a⟩ := exists_ne_zero_dotProduct_eq_zero_of_two_le hm ha
  rw [dotProduct_comm] at hv₀a
  obtain ⟨μ₀, -, hμ₀⟩ := exists_smul_of_vecMulVec_eq (h1 v₀ hv₀a) hv₀ ha
  have h2 : ∀ v : Fin m → K, a ⬝ᵥ v = 0 → X *ᵥ v = μ₀ • v := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0, Matrix.mulVec_zero, smul_zero]
    obtain ⟨μ, hμ, hμ'⟩ := exists_smul_of_vecMulVec_eq (h1 v hv) hv0 ha
    have : μ = μ₀ := by
      have h3 : μ • a = μ₀ • a := hμ'.symm.trans hμ₀
      by_contra hne
      apply ha
      have h4 : (μ - μ₀) • a = 0 := by rw [sub_smul, h3, sub_self]
      exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hne)
    rw [hμ, this]
  have h3 : ∀ v : Fin m → K, a ⬝ᵥ v = 0 →
      (X - μ₀ • (1 : Matrix (Fin m) (Fin m) K)) *ᵥ v = 0 := by
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h2 v hv, sub_self]
  obtain ⟨w, hw⟩ := exists_vecMulVec_of_forall_mulVec_eq_zero ha _ h3
  refine ⟨μ₀, w, ?_, by rw [← hw]; abel⟩
  have h5 : X = μ₀ • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec w a := by rw [← hw]; abel
  have h4 : a ᵥ* X = μ₀ • a := hμ₀
  rw [h5, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]
    at h4
  have h6 : (a ⬝ᵥ w) • a = 0 := add_eq_left.1 h4
  exact (smul_eq_zero.1 h6).resolve_right ha

end CFSG.RankThree.GF2n.Stroth80
