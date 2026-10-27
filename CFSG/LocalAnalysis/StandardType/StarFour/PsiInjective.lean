module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.StandardType.StarFour

theorem pow_bijective_of_coprime {F : Type*} [Field F] [Finite F] {n : ℕ}
    (h : Nat.Coprime n (Nat.card F - 1)) : Function.Bijective (fun μ : Fˣ => μ ^ n) := by
  have h' : (Nat.card Fˣ).Coprime n := by
    rw [Nat.card_units]
    exact h.symm
  simpa only using h'.pow_left_bijective

theorem center_specialLinearGroup_eq_bot_of_coprime {F : Type*} [Field F] [Finite F] {n : ℕ}
    (h : Nat.Coprime n (Nat.card F - 1)) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
  by_cases hn : n = 0
  · subst n
    exact Matrix.SpecialLinearGroup.center_eq_bot_of_subsingleton
  · refine le_antisymm ?_ bot_le
    intro A hA
    rw [Subgroup.mem_bot]
    obtain ⟨r, hrpow, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hrpow
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hn] at hrpow
      exact zero_ne_one hrpow
    let u : Fˣ := Units.mk0 r hr0
    have hu : u ^ n = 1 := by
      apply Units.ext
      simpa [u] using hrpow
    have hu1 : u = 1 :=
      (pow_bijective_of_coprime h).injective (hu.trans (one_pow n).symm)
    have hr1 : r = 1 := by
      have := congrArg (fun x : Fˣ => (x : F)) hu1
      simpa [u] using this
    have hA1 : A = 1 := by
      apply Subtype.ext
      rw [← hrA, hr1]
      simp
    exact hA1

theorem psi_injective_of_ker_le_center {F : Type*} [Field F] [Finite F] {n : ℕ}
    (h : Nat.Coprime n (Nat.card F - 1)) {X : Type*} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff ψ]
  refine le_antisymm ?_ bot_le
  simpa only [center_specialLinearGroup_eq_bot_of_coprime h] using hker

end CFSG.StandardType.StarFour
