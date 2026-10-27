module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H.L3Nine

open Polynomial

theorem two_eq_zero_of_algebra (K : Type*) [Field K] [CharP K 2] {A : Type*} [Ring A]
    [Algebra K A] : (2 : A) = 0 := by
  rw [← map_ofNat (algebraMap K A) 2, CharTwo.two_eq_zero, map_zero]

theorem add_self_eq_zero_of_algebra (K : Type*) [Field K] [CharP K 2] {A : Type*} [Ring A]
    [Algebra K A] (x : A) : x + x = 0 := by
  rw [← two_mul, two_eq_zero_of_algebra K, zero_mul]

theorem add_pow_two_pow_of_commute (K : Type*) [Field K] [CharP K 2] {A : Type*} [Ring A]
    [Algebra K A] {u v : A} (h : Commute u v) (k : ℕ) :
    (u + v) ^ 2 ^ k = u ^ 2 ^ k + v ^ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ 2 k, pow_mul, ih, ((h.pow_pow _ _).add_sq), pow_mul, pow_mul,
      two_eq_zero_of_algebra K, zero_mul, zero_mul, add_zero]

variable {K : Type*} [Field K] [CharP K 2]

section Alg

variable {A : Type*} [Ring A] [Algebra K A]

theorem pow_two_mul_card_sq_eq [Finite K] {j : ℕ} (hK : Nat.card K = 2 ^ j)
    {f : A} {t c : K} (hf : f ^ 2 = t • f + c • 1) : f ^ (2 * Nat.card K ^ 2) = f ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hQc : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hfix : ∀ a : K, a ^ Nat.card K = a := fun a => by
    rw [← hQc]
    exact FiniteField.pow_card a
  have hfrob : ∀ u v : A, Commute u v → (u + v) ^ Nat.card K = u ^ Nat.card K + v ^ Nat.card K :=
    fun u v h => by
      rw [hK]
      exact add_pow_two_pow_of_commute K h j
  have hxx := add_self_eq_zero_of_algebra K (A := A)
  set Q := Nat.card K with hQ
  set P := f ^ Q with hP
  have hPf : Commute P f := (Commute.refl f).pow_left Q
  have hP2 : P ^ 2 = t • P + c • 1 := by
    have hc : Commute (t • f) (c • (1 : A)) := ((Commute.one_right f).smul_right c).smul_left t
    rw [hP, ← pow_mul, mul_comm, pow_mul, hf, hfrob _ _ hc, smul_pow, smul_pow, one_pow, hfix,
      hfix]
  set δ := P + f with hδ
  have hδf : Commute δ f := hPf.add_left (Commute.refl f)
  have hδ2 : δ ^ 2 = t • δ := by
    have e1 : δ ^ 2 = P ^ 2 + f ^ 2 + (P * f + P * f) := by
      rw [hδ, sq, sq, sq, add_mul, mul_add, mul_add, ← hPf.eq]
      abel
    rw [e1, hxx, add_zero, hP2, hf, smul_add]
    rw [show t • P + c • (1 : A) + (t • f + c • 1) = t • P + t • f + (c • 1 + c • 1) by abel,
      hxx, add_zero]
  have hδpow : ∀ k : ℕ, δ ^ 2 ^ k = t ^ (2 ^ k - 1) • δ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ 2 k, pow_mul, ih, smul_pow, hδ2, smul_smul, ← pow_mul, ← pow_succ]
      congr 2
      omega
  have hfδ : P = f + δ := by
    rw [hδ, add_comm P f, ← add_assoc, hxx, zero_add]
  set ε := (1 + t ^ (Q - 1)) • δ with hε
  have hδQ : δ ^ Q = t ^ (Q - 1) • δ := by
    rw [hK]
    exact hδpow j
  have hfQ2 : f ^ Q ^ 2 = f + ε := by
    have h1 : f ^ Q ^ 2 = (f + δ) ^ Q := by rw [sq, pow_mul, ← hP, hfδ]
    rw [h1, hfrob _ _ hδf.symm, ← hP, hδQ, hfδ, hε, add_smul, one_smul, add_assoc]
  have hε2 : ε ^ 2 = 0 := by
    have h0 : (1 + t ^ (Q - 1)) ^ 2 * t = 0 := by
      by_cases ht : t = 0
      · rw [ht, mul_zero]
      · have h1 : t ^ (Q - 1) = 1 := by
          rw [← hQc]
          exact FiniteField.pow_card_sub_one_eq_one t ht
        rw [h1, CharTwo.add_self_eq_zero, sq, zero_mul, zero_mul]
    rw [hε, smul_pow, hδ2, smul_smul, h0, zero_smul]
  have hεf : Commute ε f := hδf.smul_left _
  rw [mul_comm, pow_mul, hfQ2, sq, add_mul, mul_add, mul_add, ← hεf.eq, ← sq ε, hε2, add_zero,
    add_assoc, hxx, add_zero, sq]

end Alg

section Lin

variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [CharP K 2] in
theorem exists_sq_eq_of_finrank_le_two (hE : Module.finrank K E ≤ 2) (S : Module.End K E) :
    ∃ t c : K, S ^ 2 = t • S + c • 1 := by
  classical
  set p : K[X] := X ^ (2 - Module.finrank K E) * S.charpoly with hp
  have hmon : p.Monic := (monic_X_pow _).mul (LinearMap.charpoly_monic S)
  have hdeg : p.natDegree = 2 := by
    rw [hp, (monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic S), natDegree_X_pow,
      LinearMap.charpoly_natDegree]
    omega
  have hS : aeval S p = 0 := by
    rw [hp, map_mul, LinearMap.aeval_self_charpoly, mul_zero]
  have h2 : p.coeff 2 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  have hsum : p = C (p.coeff 0) + C (p.coeff 1) * X + X ^ 2 := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow, hdeg]
    simp [Finset.sum_range_succ, h2]
  rw [hsum] at hS
  simp only [map_add, map_mul, aeval_C, aeval_X, map_pow] at hS
  refine ⟨-p.coeff 1, -p.coeff 0, ?_⟩
  have h3 : S ^ 2 = -(algebraMap K (Module.End K E) (p.coeff 0) +
      algebraMap K (Module.End K E) (p.coeff 1) * S) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hS)
  rw [h3]
  simp only [Algebra.smul_def, mul_one, map_neg, neg_mul]
  abel

variable [Finite K]

theorem pow_four_mul_card_sq_eq {j : ℕ} (hK : Nat.card K = 2 ^ j)
    (T : Module.End K E) {W : Submodule K E} (hW : ∀ x ∈ W, T x ∈ W)
    (hW₁ : Module.finrank K W ≤ 2) (hW₂ : Module.finrank K (E ⧸ W) ≤ 2) :
    T ^ (4 * Nat.card K ^ 2) = T ^ 4 := by
  set N := 2 * Nat.card K ^ 2 with hN
  have hW' : W ≤ W.comap T := hW
  obtain ⟨t₁, c₁, h₁⟩ := exists_sq_eq_of_finrank_le_two hW₁ (T.restrict hW)
  have hA₁ := pow_two_mul_card_sq_eq hK h₁
  have hres : ∀ (k : ℕ) (x : W), (((T.restrict hW) ^ k) x : E) = (T ^ k) (x : E) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have hon : ∀ w ∈ W, (T ^ N) w = (T ^ 2) w := by
    intro w hw
    have := congrArg (fun S : Module.End K W => (S ⟨w, hw⟩ : E)) hA₁
    simp only [hres] at this
    exact this
  obtain ⟨t₂, c₂, h₂⟩ := exists_sq_eq_of_finrank_le_two hW₂ (W.mapQ W T hW')
  have hA₂ := pow_two_mul_card_sq_eq hK h₂
  have hquo : ∀ (k : ℕ) (u : E), ((W.mapQ W T hW') ^ k) (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((T ^ k) u) := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, ih, Submodule.mapQ_apply, pow_succ',
        Module.End.mul_apply]
  have hmod : ∀ u : E, (T ^ N) u - (T ^ 2) u ∈ W := by
    intro u
    have := congrArg (fun S : Module.End K (E ⧸ W) => S (Submodule.Quotient.mk u)) hA₂
    simp only [hquo] at this
    exact (Submodule.Quotient.eq W).mp this
  have hxx := fun x : E => (two_smul K x).symm.trans (by rw [CharTwo.two_eq_zero, zero_smul])
  refine LinearMap.ext fun u => ?_
  set a := (T ^ N) u - (T ^ 2) u with ha
  have hTu : (T ^ N) u = (T ^ 2) u + a := by rw [ha, add_sub_cancel]
  have hcomm : (T ^ N) ((T ^ 2) u) = (T ^ 2) ((T ^ N) u) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add, add_comm]
  calc (T ^ (4 * Nat.card K ^ 2)) u = (T ^ N) ((T ^ N) u) := by
        rw [← Module.End.mul_apply, ← pow_add, hN]
        ring_nf
    _ = (T ^ 2) ((T ^ 2) u) + ((T ^ 2) a + (T ^ 2) a) := by
        rw [hTu, map_add, hcomm, hon a (hmod u), hTu, map_add]
        abel
    _ = (T ^ 4) u := by
        rw [hxx, add_zero, ← Module.End.mul_apply, ← pow_add]
