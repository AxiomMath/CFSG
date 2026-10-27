module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

/-!
# Huppert III.1.3

Two power identities for commuting commutators.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u

/--
Huppert III, Lemma 1.3(a). If the commutator of `a` and `b` commutes with `a`,
then `⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n` for every integer `n`.
-/
public theorem huppert_III_1_3_a
    {G : Type u} [Group G] (a b : G)
    (hcomm : Commute ⁅a, b⁆ a) (n : ℤ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  have hnat : ∀ k : ℕ, ⁅a ^ k, b⁆ = ⁅a, b⁆ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        ⁅a ^ (k + 1), b⁆ =
            a ^ k * ⁅a, b⁆ * (a ^ k)⁻¹ * ⁅a ^ k, b⁆ := by
          rw [pow_succ]
          simp only [commutatorElement_def]
          group
        _ = ⁅a, b⁆ * ⁅a, b⁆ ^ k := by
          rw [ih, ← (hcomm.pow_right k).eq]
          group
        _ = ⁅a, b⁆ ^ (k + 1) := by
          rw [pow_succ]
          exact (Commute.self_pow _ _).eq
  have hinv (x : G) (hx : Commute ⁅x, b⁆ x) :
      ⁅x⁻¹, b⁆ = ⁅x, b⁆⁻¹ := by
    have hconj : b * x⁻¹ * b⁻¹ * x = ⁅x, b⁆ := by
      calc
        b * x⁻¹ * b⁻¹ * x = x⁻¹ * (⁅x, b⁆ * x) := by
          simp only [commutatorElement_def]
          group
        _ = x⁻¹ * (x * ⁅x, b⁆) := by rw [hx.eq]
        _ = ⁅x, b⁆ := by group
    calc
      ⁅x⁻¹, b⁆ = (b * x⁻¹ * b⁻¹ * x)⁻¹ := by
        simp only [commutatorElement_def]
        group
      _ = ⁅x, b⁆⁻¹ := by rw [hconj]
  cases n with
  | ofNat k => simpa using hnat k
  | negSucc k =>
      have hxcomm : Commute ⁅a ^ (k + 1), b⁆ (a ^ (k + 1)) := by
        rw [hnat]
        exact hcomm.pow_pow _ _
      calc
        ⁅a ^ Int.negSucc k, b⁆ = ⁅(a ^ (k + 1))⁻¹, b⁆ := by
          rw [zpow_negSucc]
        _ = ⁅a ^ (k + 1), b⁆⁻¹ := hinv _ hxcomm
        _ = (⁅a, b⁆ ^ (k + 1))⁻¹ := by rw [hnat]
        _ = ⁅a, b⁆ ^ Int.negSucc k := by rw [zpow_negSucc]

/--
Huppert III, Lemma 1.3(b). If the commutator of `a` and `b` commutes with both
`a` and `b`, then the displayed class-two power formula holds for every natural
number `n`.
-/
public theorem huppert_III_1_3_b
    {G : Type u} [Group G] (a b : G)
    (hcomm_a : Commute ⁅a, b⁆ a) (hcomm_b : Commute ⁅a, b⁆ b) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ Nat.choose n 2 := by
  have hdcomm_a : Commute ⁅b, a⁆ a := by
    rw [← commutatorElement_inv]
    exact hcomm_a.inv_left
  have hdcomm_b : Commute ⁅b, a⁆ b := by
    rw [← commutatorElement_inv]
    exact hcomm_b.inv_left
  induction n with
  | zero => simp
  | succ n ih =>
      have hcommutator : ⁅b ^ n, a⁆ = ⁅b, a⁆ ^ n := by
        simpa using huppert_III_1_3_a b a hdcomm_b (n : ℤ)
      have hba : b ^ n * a = a * b ^ n * ⁅b, a⁆ ^ n := by
        calc
          b ^ n * a = ⁅b, a⁆ ^ n * a * b ^ n := by
            rw [← hcommutator]
            simp only [commutatorElement_def]
            group
          _ = a * ⁅b, a⁆ ^ n * b ^ n := by
            rw [(hdcomm_a.pow_left n).eq]
          _ = a * (⁅b, a⁆ ^ n * b ^ n) := by group
          _ = a * (b ^ n * ⁅b, a⁆ ^ n) := by
            rw [(hdcomm_b.pow_pow n n).eq]
          _ = a * b ^ n * ⁅b, a⁆ ^ n := by group
      rw [pow_succ, ih]
      calc
        (a ^ n * b ^ n * ⁅b, a⁆ ^ Nat.choose n 2) * (a * b) =
            a ^ n * b ^ n * a * b * ⁅b, a⁆ ^ Nat.choose n 2 := by
          calc
            _ = a ^ n * b ^ n * (⁅b, a⁆ ^ Nat.choose n 2 * a) * b := by group
            _ = a ^ n * b ^ n * (a * ⁅b, a⁆ ^ Nat.choose n 2) * b := by
              rw [(hdcomm_a.pow_left (Nat.choose n 2)).eq]
            _ = a ^ n * b ^ n * a * (⁅b, a⁆ ^ Nat.choose n 2 * b) := by group
            _ = a ^ n * b ^ n * a * (b * ⁅b, a⁆ ^ Nat.choose n 2) := by
              rw [(hdcomm_b.pow_left (Nat.choose n 2)).eq]
            _ = _ := by group
        _ = a ^ n * (b ^ n * a) * b * ⁅b, a⁆ ^ Nat.choose n 2 := by group
        _ = a ^ n * (a * b ^ n * ⁅b, a⁆ ^ n) * b *
              ⁅b, a⁆ ^ Nat.choose n 2 := by rw [hba]
        _ = a ^ (n + 1) * b ^ (n + 1) *
              ⁅b, a⁆ ^ Nat.choose (n + 1) 2 := by
          rw [pow_succ a, pow_succ b]
          rw [show Nat.choose (n + 1) 2 = n + Nat.choose n 2 by simp [Nat.choose]]
          rw [pow_add]
          calc
            _ = a ^ n * a * b ^ n * (⁅b, a⁆ ^ n * b) *
                  ⁅b, a⁆ ^ Nat.choose n 2 := by group
            _ = a ^ n * a * b ^ n * (b * ⁅b, a⁆ ^ n) *
                  ⁅b, a⁆ ^ Nat.choose n 2 := by
              rw [(hdcomm_b.pow_left n).eq]
            _ = _ := by group

end External
end CFSG.BenderSuzuki
