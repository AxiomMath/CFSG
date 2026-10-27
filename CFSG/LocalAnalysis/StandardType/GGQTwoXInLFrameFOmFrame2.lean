module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2

public section

namespace CFSG.StandardType

namespace QTwoOmFrame

open CFSG.StandardType.TraceFrame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def framePsi {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {n : ℕ} (a : Fin n → M) (c : M) (τ : M ≃+* M) :
    (Fin n → M) ≃ₗ[K] (Fin n → M) := by
  classical
  exact LinearEquiv.piCongrRight fun i =>
    if a i = c then LinearEquiv.refl K M else (tauAlg (τ := τ) hK).toLinearEquiv

lemma framePsi_apply {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    [DecidableEq M] (hK : Nat.card K = 2) {n : ℕ} (a : Fin n → M) (c : M) (τ : M ≃+* M)
    (d : Fin n → M) (i : Fin n) :
    framePsi (K := K) hK a c τ d i = if a i = c then d i else τ (d i) := by
  classical
  by_cases h : a i = c <;> simp [framePsi, h, tauAlg]

noncomputable def frameTwist {M : Type} [Field M] {n : ℕ} (a : Fin n → M) (c : M)
    (τ : M ≃+* M) (b : Fin n → M) : Fin n → M := by
  classical
  exact fun i => if a i = c then b i else τ (b i)

lemma frameTwist_invol {M : Type} [Field M] {n : ℕ} (a : Fin n → M) (c : M)
    (τ : M ≃+* M)
    (hτ : ∀ y, τ (τ y) = y) (b : Fin n → M) :
    frameTwist a c τ (frameTwist a c τ b) = b := by
  classical
  ext i
  by_cases h : a i = c <;> simp [frameTwist, h, hτ]

lemma frameTwist_cube {M : Type} [Field M] {n : ℕ} (a : Fin n → M) (c : M)
    (τ : M ≃+* M)
    {b : Fin n → M} (hb : ∀ i, b i ^ 3 = 1) :
    ∀ i, frameTwist a c τ b i ^ 3 = 1 := by
  classical
  intro i
  by_cases h : a i = c
  · simpa [frameTwist, h] using hb i
  · rw [frameTwist, if_neg h, ← map_pow, hb i, map_one]

lemma framePsi_mul {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    [DecidableEq M] (hK : Nat.card K = 2) {n : ℕ} (a : Fin n → M) (c : M) (τ : M ≃+* M)
    (b d : Fin n → M) :
    framePsi (K := K) hK a c τ (fun i => b i * d i) =
      fun i => frameTwist a c τ b i * framePsi (K := K) hK a c τ d i := by
  classical
  ext i
  rw [framePsi_apply, framePsi_apply]
  by_cases h : a i = c <;> simp [frameTwist, h, map_mul]

lemma frameTwist_const {M : Type} [Field M] {n : ℕ} {a : Fin n → M} {c : M}
    {τ : M ≃+* M} (hc : c ^ 2 ≠ c)
    (hroots : ∀ i, a i = c ∨ a i = c ^ 2) (hτ2 : ∀ y, τ y = y ^ 2) :
    frameTwist a c τ (fun _ => c) = a := by
  classical
  ext i
  rcases hroots i with h | h
  · rw [frameTwist, if_pos h, h]
  · have hne : a i ≠ c := by rw [h]; exact fun hh => hc hh
    rw [frameTwist, if_neg hne, hτ2, h]

end QTwoOmFrame

end CFSG.StandardType

end
