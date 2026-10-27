module

import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster

variable {L : Type*} [AddCommGroup L]

theorem rootless_short_sums (h : L →+ L →+ ℤ) (hsymm : ∀ x y, h x y = h y x)
    (hmin : ∀ w, w ≠ 0 → 4 ≤ h w w) {u v : L} (hu : h u u = 4) (hv : h v v = 4)
    (huv : u ≠ v) (huv' : u ≠ -v) :
    (h u v = -2 ∨ h u v = -1 ∨ h u v = 0 ∨ h u v = 1 ∨ h u v = 2) ∧
      ((∃ w t : L, u + v = w + 2 • t ∧ h w w = 4) ↔ (h u v = 2 ∨ h u v = -2)) ∧
      (h u v = 2 → h (u - v) (u - v) = 4 ∧ u + v = (u - v) + 2 • v) ∧
      (h u v = -2 → h (u + v) (u + v) = 4) := by
  have hvu : h v u = h u v := hsymm v u
  have hsum : h (u + v) (u + v) = 8 + 2 * h u v := by
    simp only [map_add, AddMonoidHom.add_apply, hu, hv, hvu]
    ring
  have hdiff : h (u - v) (u - v) = 8 - 2 * h u v := by
    simp only [map_sub, AddMonoidHom.sub_apply, hu, hv, hvu]
    ring
  have hsum0 : u + v ≠ 0 := fun h0 => huv' (eq_neg_of_add_eq_zero_left h0)
  have hdiff0 : u - v ≠ 0 := fun h0 => huv (sub_eq_zero.1 h0)
  have h1 := hmin _ hsum0
  have h2 := hmin _ hdiff0
  have hrange : -2 ≤ h u v ∧ h u v ≤ 2 := by constructor <;> linarith
  have hu2v : u + v = (u - v) + 2 • v := by rw [two_nsmul]; abel
  refine ⟨by omega, ⟨?_, ?_⟩, fun h2 => ⟨by rw [hdiff, h2]; norm_num, hu2v⟩,
    fun h2 => by rw [hsum, h2]; norm_num⟩
  · rintro ⟨w, t, hwt, hw⟩
    have hwt' : h w t = h t w := hsymm w t
    have hnorm : h (u + v) (u + v) = h w w + 4 * h w t + 4 * h t t := by
      rw [hwt]
      simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
        ← hwt']
      ring
    rw [hsum, hw] at hnorm
    by_contra hne
    have h0 : h u v = 0 := by
      have : h u v ≠ 2 ∧ h u v ≠ -2 := by tauto
      omega
    have hb : t ≠ 0 := by
      rintro rfl
      rw [hwt] at hsum
      simp at hsum
      rw [hw, h0] at hsum
      norm_num at hsum
    have ha : w + t ≠ 0 := by
      intro hat
      have : t = -w := eq_neg_of_add_eq_zero_right hat
      subst this
      have : u + v = -w := by rw [hwt, two_nsmul]; abel
      rw [this] at hsum
      simp only [map_neg, AddMonoidHom.neg_apply, neg_neg] at hsum
      rw [hw, h0] at hsum
      norm_num at hsum
    have hpar : h (w + t) (w + t) + h t t = 6 := by
      simp only [map_add, AddMonoidHom.add_apply, ← hwt']
      rw [h0] at hnorm
      linarith
    have := hmin _ ha
    have := hmin _ hb
    linarith
  · rintro (h2 | h2)
    · exact ⟨u - v, v, hu2v, by rw [hdiff, h2]; norm_num⟩
    · exact ⟨u + v, 0, by simp, by rw [hsum, h2]; norm_num⟩

end CFSG.Monster
