module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG

namespace FiveTransitive.InvolutionProductSupport
open Equiv

private theorem pow_apply_fixed {X : Type*} (r : Perm X) (x : X)
    (hr : r x = x) (k : ℕ) : (r ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pow_succ, Perm.mul_apply, hr, ih]

private theorem even_power_fixed_of_square_fixed {X : Type*}
    (r : Perm X) (k : ℕ) (x : X) (h : (r ^ 2) x = x) :
    (r ^ (2 * k)) x = x := by
  rw [pow_mul]
  exact pow_apply_fixed _ x h k

private theorem involution_power_fixed_of_cube_fixed {X : Type*}
    (r : Perm X) (k : ℕ) (hpow : (r ^ k) ^ 2 = 1)
    (x : X) (h : (r ^ 3) x = x) : (r ^ k) x = x := by
  have hc : ((r ^ k) ^ 3) x = x := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact pow_apply_fixed _ x h k
  simpa only [show 3 = 2 + 1 from rfl, pow_succ, hpow, one_mul] using hc

private def neighbor {X : Type*} [DecidableEq X] (s t : Perm X) (x : X) : X :=
  if s x = x then t x else s x

private theorem neighbor_mem_inter {X : Type*} [Fintype X] [DecidableEq X]
    (s t : Perm X) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (k : ℕ)
    (x : X) (hx : x ∈ ((s * t) ^ (2 * k)).support)
    (hout : x ∉ s.support ∩ t.support) : neighbor s t x ∈ s.support ∩ t.support := by
  have hsx : ∀ z, s (s z) = z := fun z => congrArg (fun q : Perm X => q z) hs
  have htx : ∀ z, t (t z) = z := fun z => congrArg (fun q : Perm X => q z) ht
  have hmove := Perm.mem_support.mp hx
  by_cases hsf : s x = x
  · have htm : t x ≠ x := by
      intro htf
      apply hmove
      apply pow_apply_fixed
      simp only [Perm.mul_apply, htf, hsf]
    have hsm : s (t x) ≠ t x := by
      intro hsf'
      apply hmove
      apply even_power_fixed_of_square_fixed
      simp only [pow_two, Perm.mul_apply, hsf', htx, hsf]
    simpa only [neighbor, if_pos hsf, Finset.mem_inter, Perm.mem_support] using
      And.intro hsm (fun h => htm (t.injective h))
  · have htf : t x = x := by
      by_contra htm
      exact hout (Finset.mem_inter.mpr ⟨Perm.mem_support.mpr hsf, Perm.mem_support.mpr htm⟩)
    have htm : t (s x) ≠ s x := by
      intro htf'
      apply hmove
      apply even_power_fixed_of_square_fixed
      simp only [pow_two, Perm.mul_apply, htf, htf', hsx]
    simpa only [neighbor, if_neg hsf, Finset.mem_inter, Perm.mem_support] using
      And.intro (fun h => hsf (s.injective h)) htm

private theorem neighbor_injective_on_outside {X : Type*} [Fintype X] [DecidableEq X]
    (s t : Perm X) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (k : ℕ)
    (hw : ((s * t) ^ (2 * k)) ^ 2 = 1) :
    Set.InjOn (neighbor s t) (↑(((s * t) ^ (2 * k)).support \ (s.support ∩ t.support)) : Set X) := by
  have hsx : ∀ z, s (s z) = z := fun z => congrArg (fun q : Perm X => q z) hs
  have htx : ∀ z, t (t z) = z := fun z => congrArg (fun q : Perm X => q z) ht
  have hcollision (x y : X) (hxs : s x = x) (hyt : t y = y)
      (heq : t x = s y) : ((s * t) ^ 3) x = x := by
    have htz : t (s y) = x := by rw [← heq, htx]
    change s (t (s (t (s (t x))))) = x
    rw [heq, hsx, hyt, htz, hxs]
  intro x hx y hy heq
  have hx' := Finset.mem_sdiff.mp hx
  have hy' := Finset.mem_sdiff.mp hy
  by_cases hxs : s x = x <;> by_cases hys : s y = y
  · exact t.injective (by simpa only [neighbor, if_pos hxs, if_pos hys] using heq)
  · have hyt : t y = y := by
      by_contra h
      exact hy'.2 (Finset.mem_inter.mpr ⟨Perm.mem_support.mpr hys, Perm.mem_support.mpr h⟩)
    have heq' : t x = s y := by simpa only [neighbor, if_pos hxs, if_neg hys] using heq
    exact ((Perm.mem_support.mp hx'.1)
      (involution_power_fixed_of_cube_fixed _ _ hw x (hcollision x y hxs hyt heq'))).elim
  · have hxt : t x = x := by
      by_contra h
      exact hx'.2 (Finset.mem_inter.mpr ⟨Perm.mem_support.mpr hxs, Perm.mem_support.mpr h⟩)
    have heq' : t y = s x := by simpa only [neighbor, if_neg hxs, if_pos hys] using heq.symm
    exact ((Perm.mem_support.mp hy'.1)
      (involution_power_fixed_of_cube_fixed _ _ hw y (hcollision y x hys hxt heq'))).elim
  · exact s.injective (by simpa only [neighbor, if_neg hxs, if_neg hys] using heq)

theorem card_support_even_power_le {X : Type*} [Fintype X] [DecidableEq X]
    (s t : Perm X) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (k : ℕ)
    (hw : ((s * t) ^ (2 * k)) ^ 2 = 1) :
    ((s * t) ^ (2 * k)).support.card ≤ 2 * (s.support ∩ t.support).card := by
  let W := ((s * t) ^ (2 * k)).support
  let I := s.support ∩ t.support
  have hmap : (W \ I).image (neighbor s t) ⊆ I := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact neighbor_mem_inter s t hs ht k x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
  have hinj : ((W \ I).image (neighbor s t)).card = (W \ I).card :=
    Finset.card_image_of_injOn (neighbor_injective_on_outside s t hs ht k hw)
  have hle := Finset.card_le_card hmap
  have hsplit := Finset.card_sdiff_add_card_inter W I
  have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁ := W) (s₂ := I))
  change W.card ≤ 2 * I.card
  omega

end FiveTransitive.InvolutionProductSupport

end CFSG
