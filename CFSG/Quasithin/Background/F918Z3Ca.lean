module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace InvolMat

theorem add_self_eq_zero (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v]
  have h : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
  rw [show (2 : K) = 0 by simpa using h, zero_smul]

theorem neg_eq_self (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero K v)

theorem card_matrix (F : Type) [Finite F] (d : ℕ) :
    Nat.card (Matrix (Fin d) (Fin d) F) = Nat.card F ^ (d * d) := by
  show Nat.card (Fin d → Fin d → F) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

theorem card_ker_sq_of_ker_eq_range {G : Type*} [AddCommGroup G] [Finite G] (ψ : G →+ G)
    (h : ψ.ker = ψ.range) : Nat.card ψ.ker ^ 2 = Nat.card G := by
  have := AddSubgroup.card_ker_mul_card_range ψ
  rw [← h] at this
  rw [sq]
  exact this

theorem exists_split_of_forall_fixed {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (f : V →ₗ[K] V) (hf : ∀ v, f (f v) = v)
    (hker : ∀ w, f w = w → ∃ u, f u + u = w) :
    ∃ s : V →ₗ[K] V, ∀ v, s v + f (s (f v)) = v := by
  set N : V →ₗ[K] V := f + LinearMap.id with hN
  have hNv : ∀ v, N v = f v + v := fun v => rfl
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    have e1 : f v + f v = 0 := add_self_eq_zero K _
    have e2 : v + v = 0 := add_self_eq_zero K _
    have : N (N v) - 0 = (f v + f v) + (v + v) := by
      simp only [hNv, map_add, hf]; abel
    rw [e1, e2] at this; simpa using this
  have hker' : ∀ v, N v = 0 → v ∈ LinearMap.range N := by
    intro v hv
    have hfv : f v = v := by
      have : f v + v = 0 := hv
      have := eq_neg_of_add_eq_zero_left this
      rw [this, neg_eq_self K]
    obtain ⟨u, hu⟩ := hker v hfv
    exact ⟨u, hu⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective N.rangeRestrict
    (LinearMap.range_rangeRestrict N)
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (p := LinearMap.range N) g
  have hNG : ∀ w ∈ LinearMap.range N, N (G w) = w := by
    intro w hw
    have h1 : G w = g ⟨w, hw⟩ := by
      have := congrArg (fun φ => φ ⟨w, hw⟩) hG
      simpa using this
    have h2 := congrArg (fun φ => (φ ⟨w, hw⟩ : V)) hg
    simp only [LinearMap.comp_apply, LinearMap.rangeRestrict, LinearMap.codRestrict_apply,
      LinearMap.id_apply] at h2
    rw [h1]; exact h2
  obtain ⟨s, hs⟩ : ∃ s : V →ₗ[K] V, ∀ x, s x = G (x - G (N x)) + G (N x) :=
    ⟨G ∘ₗ (LinearMap.id - G ∘ₗ N) + G ∘ₗ N, fun x => by simp⟩
  have hfN : ∀ x, f x = N x - x := fun x => by rw [hNv]; abel
  have hmem : ∀ x, x - G (N x) ∈ LinearMap.range N := by
    intro x
    apply hker'
    rw [map_sub, hNG (N x) ⟨x, rfl⟩, sub_self]
  have h1 : ∀ x, N (s x) = x - G (N x) + N x := by
    intro x
    rw [hs, map_add, hNG _ (hmem x), hNG (N x) ⟨x, rfl⟩]
  have h2 : ∀ x, s (N x) = G (N x) := by
    intro x
    rw [hs, hNN, map_zero, sub_zero, add_zero]
  have h3 : ∀ x, N (s (N x)) = N x := by
    intro x
    rw [h2, hNG (N x) ⟨x, rfl⟩]
  refine ⟨s, fun v => ?_⟩
  have e1 : s v + s v = 0 := add_self_eq_zero K _
  have e2 : v + v = 0 := add_self_eq_zero K _
  rw [hfN (s (f v)), hfN v, map_sub, map_sub, h3, h1, h2]
  have key : s v + (N v - (v - G (N v) + N v) - (G (N v) - s v)) - v =
      (s v + s v) - (v + v) := by
    abel
  rw [e1, e2, sub_zero] at key
  exact sub_eq_zero.mp key

@[expose] def sumHom {F : Type} [Field F] {d : ℕ} (P Q : Matrix (Fin d) (Fin d) F) :
    Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
  AddMonoidHom.mk' (fun M => M + P * M * Qᵀ) (by
    intro a b
    simp only [mul_add, add_mul]
    abel)

theorem sumHom_apply {F : Type} [Field F] {d : ℕ} (P Q : Matrix (Fin d) (Fin d) F)
    (M : Matrix (Fin d) (Fin d) F) : sumHom P Q M = M + P * M * Qᵀ := rfl

theorem sumHom_sumHom {F : Type} [Field F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1)
    (M : Matrix (Fin d) (Fin d) F) : sumHom P Q (sumHom P Q M) = 0 := by
  have hQt : Qᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  have e1 : M + M = 0 := add_self_eq_zero F M
  have e2 : P * M * Qᵀ + P * M * Qᵀ = 0 := add_self_eq_zero F _
  have : sumHom P Q (sumHom P Q M) = (M + M) + (P * M * Qᵀ + P * M * Qᵀ) := by
    simp only [sumHom_apply, mul_add, add_mul]
    have h3 : P * (P * M * Qᵀ) * Qᵀ = M := by
      rw [← mul_assoc, ← mul_assoc, hP, one_mul, mul_assoc M, hQt, mul_one]
    rw [h3]; abel
  rw [this, e1, e2, add_zero]

theorem mem_ker_sumHom {F : Type} [Field F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (M : Matrix (Fin d) (Fin d) F) :
    M ∈ (sumHom P Q).ker ↔ P * M * Qᵀ = M := by
  rw [AddMonoidHom.mem_ker, sumHom_apply, add_eq_zero_iff_eq_neg, neg_eq_self F]
  exact eq_comm

theorem mul_eq_mul_transpose_of_fixed {F : Type} [Field F] {d : ℕ}
    {P Q M : Matrix (Fin d) (Fin d) F} (hQ : Q * Q = 1) (hM : P * M * Qᵀ = M) :
    P * M = M * Qᵀ := by
  have hQt : Qᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  calc P * M = P * M * (Qᵀ * Qᵀ) := by rw [hQt, mul_one]
    _ = (P * M * Qᵀ) * Qᵀ := by rw [mul_assoc (P * M)]
    _ = M * Qᵀ := by rw [hM]

theorem ker_sumHom_eq_range {F : Type} [Field F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1)
    (h : ∀ M : Matrix (Fin d) (Fin d) F, P * M * Qᵀ = M → ∃ N, N + P * N * Qᵀ = M) :
    (sumHom P Q).ker = (sumHom P Q).range := by
  refine le_antisymm (fun M hM => ?_) (fun M hM => ?_)
  · obtain ⟨N, hN⟩ := h M ((mem_ker_sumHom M).1 hM)
    exact ⟨N, hN⟩
  · obtain ⟨N, rfl⟩ := hM
    exact sumHom_sumHom hP hQ N

theorem card_fixed_of_ker_eq_range {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) F} (h : (sumHom P Q).ker = (sumHom P Q).range) :
    Nat.card {M : Matrix (Fin d) (Fin d) F // P * M * Qᵀ = M} ^ 2 = Nat.card F ^ (d * d) := by
  rw [← card_matrix F d, ← card_ker_sq_of_ker_eq_range _ h]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun M => (mem_ker_sumHom M).symm)

end InvolMat

open InvolMat

theorem exists_split_of_free {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P : Matrix (Fin d) (Fin d) F} (hP : P * P = 1)
    (hfree : Nat.card {w : Fin d → F // P *ᵥ w = w} ^ 2 = Nat.card F ^ d) :
    ∃ S : Matrix (Fin d) (Fin d) F, S + P * S * P = 1 := by
  set f : (Fin d → F) →ₗ[F] (Fin d → F) := P.mulVecLin with hf
  have hfv : ∀ v, f v = P *ᵥ v := fun v => rfl
  have hff : ∀ v, f (f v) = v := by
    intro v
    rw [hfv, hfv, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  set N : (Fin d → F) →ₗ[F] (Fin d → F) := f + LinearMap.id with hN
  have hNv : ∀ v, N v = f v + v := fun v => rfl
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    have e1 : f v + f v = 0 := add_self_eq_zero F _
    have e2 : v + v = 0 := add_self_eq_zero F _
    have : N (N v) - 0 = (f v + f v) + (v + v) := by
      simp only [hNv, map_add, hff]; abel
    rw [e1, e2] at this; simpa using this
  have hrange_le : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨y, rfl⟩
    exact hNN y
  have hker_iff : ∀ w, w ∈ LinearMap.ker N ↔ P *ᵥ w = w := by
    intro w
    rw [LinearMap.mem_ker, hNv, hfv, add_eq_zero_iff_eq_neg, neg_eq_self F]
  have hcard : Nat.card {w : Fin d → F // P *ᵥ w = w} = Nat.card (LinearMap.ker N) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => (hker_iff w).symm)
  have hpow := Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker N)
  have hF2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
  rw [hcard, hpow, ← pow_mul] at hfree
  have hk : Module.finrank F (LinearMap.ker N) * 2 = d := Nat.pow_right_injective hF2 hfree
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at hrn
  have hfin : Module.finrank F (LinearMap.range N) = Module.finrank F (LinearMap.ker N) := by
    omega
  have heq : LinearMap.range N = LinearMap.ker N :=
    Submodule.eq_of_le_of_finrank_eq hrange_le hfin
  have hker : ∀ w, f w = w → ∃ u, f u + u = w := by
    intro w hw
    have : w ∈ LinearMap.ker N := (hker_iff w).2 (by rw [← hfv]; exact hw)
    rw [← heq] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  obtain ⟨s, hs⟩ := exists_split_of_forall_fixed f hff hker
  refine ⟨LinearMap.toMatrix' s, ?_⟩
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  simp only [Matrix.toLin'_apply, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
  have := hs v
  rwa [hfv, hfv] at this

theorem card_fixed_of_split {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {P Q S : Matrix (Fin d) (Fin d) F} (hP : P * P = 1) (hQ : Q * Q = 1)
    (hS : S + P * S * P = 1) :
    Nat.card {M : Matrix (Fin d) (Fin d) F // P * M * Qᵀ = M} ^ 2 = Nat.card F ^ (d * d) := by
  refine card_fixed_of_ker_eq_range (ker_sumHom_eq_range hP hQ fun M hM => ?_)
  have hPM : P * M = M * Qᵀ := mul_eq_mul_transpose_of_fixed hQ hM
  refine ⟨S * M, ?_⟩
  calc S * M + P * (S * M) * Qᵀ = S * M + P * S * (P * M) := by
        rw [hPM, ← mul_assoc, mul_assoc (P * S) M]
    _ = (S + P * S * P) * M := by rw [add_mul, mul_assoc (P * S) P M]
    _ = M := by rw [hS, one_mul]

end CFSG.Quasithin
