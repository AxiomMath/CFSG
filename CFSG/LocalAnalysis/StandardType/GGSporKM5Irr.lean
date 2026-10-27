module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.SporadicShape

open scoped Matrix

@[expose] def m5tMat : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![0, 0, 1, 0, 0, 3; 3, 4, 0, 0, 3, 0; 1, 2, 4, 2, 0, 1; 3, 0, 0, 1, 0, 2; 4, 0, 0, 0, 0, 0;
    1, 0, 0, 2, 3, 0]

private def m5tMatInvSubOne : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![3, 4, 4, 4, 0, 1; 0, 2, 0, 0, 1, 0; 0, 2, 2, 3, 0, 3; 2, 1, 1, 0, 4, 2; 2, 1, 1, 1, 4, 4;
    3, 4, 4, 2, 0, 1]

private theorem m5tMat_pow_seven : m5tMat ^ 7 = 1 := by
  decide +kernel

private theorem eq_zero_of_vecMul_eq {v : Fin 6 → ZMod 5} (h : v ᵥ* m5tMat = v) : v = 0 := by
  have hmul : (m5tMat - 1) * m5tMatInvSubOne = 1 := by decide +kernel
  have hzero : v ᵥ* (m5tMat - 1) = 0 := by
    rw [Matrix.vecMul_sub, h, Matrix.vecMul_one, sub_self]
  calc v = v ᵥ* 1 := (Matrix.vecMul_one v).symm
    _ = v ᵥ* ((m5tMat - 1) * m5tMatInvSubOne) := by rw [hmul]
    _ = v ᵥ* (m5tMat - 1) ᵥ* m5tMatInvSubOne := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [hzero, Matrix.zero_vecMul]

private def m5tAct (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ∈ W) : Function.End W :=
  fun v => ⟨v.1 ᵥ* m5tMat, hT v.1 v.2⟩

private theorem m5tAct_pow_apply (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ∈ W) (n : ℕ) (v : W) :
    ((m5tAct W hT ^ n) v : Fin 6 → ZMod 5) = v.1 ᵥ* m5tMat ^ n := by
  induction n generalizing v with
  | zero =>
      rw [pow_zero]
      change (v : Fin 6 → ZMod 5) = v.1 ᵥ* m5tMat ^ 0
      rw [pow_zero, Matrix.vecMul_one]
  | succ n ih =>
      rw [pow_succ]
      change ((m5tAct W hT ^ n) (m5tAct W hT v) : Fin 6 → ZMod 5) = v.1 ᵥ* m5tMat ^ (n + 1)
      rw [ih (m5tAct W hT v), pow_succ']
      change (v.1 ᵥ* m5tMat) ᵥ* m5tMat ^ n = v.1 ᵥ* (m5tMat * m5tMat ^ n)
      rw [Matrix.vecMul_vecMul]

private theorem natCard_modEq_one (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ∈ W) : Nat.card W ≡ 1 [MOD 7] := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hf : m5tAct W hT ^ 7 ^ 1 = 1 := by
    rw [pow_one]
    funext v
    apply Subtype.ext
    rw [m5tAct_pow_apply, m5tMat_pow_seven, Matrix.vecMul_one, Function.End.one_def]
    rfl
  have hfix : Function.fixedPoints (m5tAct W hT : W → W) = {0} := by
    ext v
    constructor
    · intro hv
      have h1 : v.1 ᵥ* m5tMat = v.1 := by
        have := congrArg Subtype.val hv
        simpa [m5tAct] using this
      exact Subtype.ext (eq_zero_of_vecMul_eq h1)
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      apply Subtype.ext
      simp [m5tAct]
  have hcard : Nat.card (Function.fixedPoints (m5tAct W hT : W → W)) = 1 := by
    rw [Nat.card_coe_set_eq, hfix]
    exact Set.ncard_singleton 0
  have h := Equiv.Perm.card_fixedPoints_modEq (f := m5tAct W hT) (p := 7) (n := 1) hf
  simp only [← Nat.card_eq_fintype_card] at h
  rw [hcard] at h
  exact h

private theorem m5t_five_pow_modeq_one {d : ℕ} (hd : d ≤ 6) (h : 5 ^ d ≡ 1 [MOD 7]) :
    d = 0 ∨ d = 6 := by
  interval_cases d
  · left; rfl
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · right; rfl

private theorem finrank_eq_zero_or_six (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ∈ W) :
    Module.finrank (ZMod 5) W = 0 ∨ Module.finrank (ZMod 5) W = 6 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : 5 ^ Module.finrank (ZMod 5) W = Nat.card W :=
    FiniteField.pow_finrank_eq_natCard 5 W
  have hle : Module.finrank (ZMod 5) W ≤ 6 := by
    have h1 := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at h1
  have hm : 5 ^ Module.finrank (ZMod 5) W ≡ 1 [MOD 7] := by
    rw [hcard]
    exact natCard_modEq_one W hT
  exact m5t_five_pow_modeq_one hle hm

private theorem m5t_mul_modeq_one {k : ℕ} (hk : ¬ 7 ∣ k) : ∃ n, (k * n) % 7 = 1 := by
  have hlt : k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hne : k % 7 ≠ 0 := fun h => hk (Nat.dvd_iff_mod_eq_zero.mpr h)
  interval_cases hk7 : k % 7
  · exact (hne rfl).elim
  · exact ⟨1, by omega⟩
  · exact ⟨4, by omega⟩
  · exact ⟨5, by omega⟩
  · exact ⟨2, by omega⟩
  · exact ⟨3, by omega⟩
  · exact ⟨6, by omega⟩

theorem m5_quot_irreducible (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases finrank_eq_zero_or_six W hT with h | h
  · left
    exact (Submodule.finrank_eq_zero).mp h
  · right
    exact Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])

theorem m5_quot_irreducible_pow {k : ℕ} (hk : ¬ 7 ∣ k) (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ^ k ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨n, hn⟩ := m5t_mul_modeq_one hk
  have hkpow : (m5tMat ^ k) ^ n = m5tMat := by
    rw [← pow_mul]
    obtain ⟨q, hq⟩ : ∃ q, k * n = 7 * q + 1 := by
      refine ⟨k * n / 7, ?_⟩
      have h := Nat.div_add_mod (k * n) 7
      omega
    rw [hq, pow_succ, pow_mul, m5tMat_pow_seven, one_pow, one_mul]
  have hinv : ∀ v ∈ W, v ᵥ* m5tMat ∈ W := by
    intro v hv
    have hp : ∀ m, v ᵥ* (m5tMat ^ k) ^ m ∈ W := by
      intro m
      induction m with
      | zero => rw [pow_zero, Matrix.vecMul_one]; exact hv
      | succ m ih =>
          rw [pow_succ, ← Matrix.vecMul_vecMul]
          exact hT _ ih
    have := hp n
    rwa [hkpow] at this
  exact m5_quot_irreducible W hinv

theorem m5_quot_irreducible_four (W : Submodule (ZMod 5) (Fin 6 → ZMod 5))
    (hT : ∀ v ∈ W, v ᵥ* m5tMat ^ 4 ∈ W) : W = ⊥ ∨ W = ⊤ :=
  m5_quot_irreducible_pow (by norm_num) W hT

end CFSG.StandardType.SporadicShape
