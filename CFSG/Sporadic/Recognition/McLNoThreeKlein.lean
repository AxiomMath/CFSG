module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup

variable {G : Type*} [Group G]

theorem conj_mem_center_of_mem_normalizer {W : Subgroup G} {s x : G}
    (hs : s ∈ normalizer (W : Set G)) (hx : x ∈ W ⊓ centralizer (W : Set G)) :
    s * x * s⁻¹ ∈ W ⊓ centralizer (W : Set G) := by
  obtain ⟨hxW, hxC⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hs x).1 hxW, mem_centralizer_iff.2 fun w hw => ?_⟩
  have hw' : s⁻¹ * w * s ∈ W := by
    have h := (mem_normalizer_iff.1 (inv_mem hs) w).1 hw
    rwa [inv_inv] at h
  have hc := mem_centralizer_iff.1 hxC _ hw'
  calc w * (s * x * s⁻¹) = s * ((s⁻¹ * w * s) * x) * s⁻¹ := by group
    _ = s * (x * (s⁻¹ * w * s)) * s⁻¹ := by rw [hc]
    _ = s * x * s⁻¹ * w := by group

theorem center_comm {W : Subgroup G} {x y : G} (hx : x ∈ W ⊓ centralizer (W : Set G))
    (hy : y ∈ W ⊓ centralizer (W : Set G)) : x * y = y * x :=
  mem_centralizer_iff.1 (mem_inf.1 hy).2 x (mem_inf.1 hx).1

theorem conj_eq_inv_of_no_fixed {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {z : G}
    (hz2 : z ^ 2 = 1) (hzA : ∀ x ∈ A, z * x * z⁻¹ ∈ A)
    (hfix : ∀ x ∈ A, x * z = z * x → x = 1) : ∀ x ∈ A, z * x * z⁻¹ = x⁻¹ := by
  intro x hx
  have hc : x * (z * x * z⁻¹) ∈ A := A.mul_mem hx (hzA x hx)
  have hcz : x * (z * x * z⁻¹) * z = z * (x * (z * x * z⁻¹)) := by
    have h1 : z * (x * (z * x * z⁻¹)) = (z * x * z⁻¹) * (z * z * x * z⁻¹ * z⁻¹) * z := by group
    have hzz : z * z = 1 := by rw [← pow_two, hz2]
    have h2 : z * z * x * z⁻¹ * z⁻¹ = x := by
      calc z * z * x * z⁻¹ * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
        _ = x := by rw [hzz, one_mul, inv_one, mul_one]
    rw [h1, h2, hA _ (hzA x hx) _ hx]
  have h := hfix _ hc hcz
  calc z * x * z⁻¹ = x⁻¹ * (x * (z * x * z⁻¹)) := by group
    _ = x⁻¹ := by rw [h, mul_one]

theorem exists_orderOf_three_comm [Finite G] {S W : Subgroup G} (hW : IsPGroup 3 ↥W)
    (hne : W ≠ ⊥) (hn : S ≤ normalizer (W : Set G)) {z t : G} (hz : z ∈ S) (ht : t ∈ S)
    (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1) :
    ∃ y ∈ W, orderOf y = 3 ∧ (y * z = z * y ∨ y * t = t * y ∨ y * (z * t) = (z * t) * y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := W ⊓ centralizer (W : Set G)
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => center_comm hx hy
  have hAS : ∀ s ∈ S, ∀ x ∈ A, s * x * s⁻¹ ∈ A := fun s hs x hx =>
    conj_mem_center_of_mem_normalizer (hn hs) hx
  have hAne : A ≠ ⊥ := by
    have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hne
    have := hW.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : ↥(center ↥W))
    have hc1 : ((c : ↥W) : G) ≠ 1 := by
      intro h
      exact hc (Subtype.ext (Subtype.ext h))
    intro hA
    have hmem : ((c : ↥W) : G) ∈ A := by
      refine mem_inf.2 ⟨(c : ↥W).2, mem_centralizer_iff.2 fun w hw => ?_⟩
      have := (mem_center_iff.1 c.2) ⟨w, hw⟩
      exact congrArg Subtype.val this
    rw [hA, mem_bot] at hmem
    exact hc1 hmem
  have key : ∃ x ∈ A, x ≠ 1 ∧ (x * z = z * x ∨ x * t = t * x ∨ x * (z * t) = (z * t) * x) := by
    by_contra hno
    push Not at hno
    have hzinv := conj_eq_inv_of_no_fixed hAc hz2 (hAS z hz)
      (fun x hx hxz => by by_contra h1; exact (hno x hx h1).1 hxz)
    have htinv := conj_eq_inv_of_no_fixed hAc ht2 (hAS t ht)
      (fun x hx hxt => by by_contra h1; exact (hno x hx h1).2.1 hxt)
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    apply (hno x x.2 hx1').2.2
    have e : z * t * (x : G) * (z * t)⁻¹ = x := by
      calc z * t * (x : G) * (z * t)⁻¹ = z * (t * x * t⁻¹) * z⁻¹ := by group
        _ = x := by
          rw [htinv _ x.2, show z * (x : G)⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ by group, hzinv _ x.2,
            inv_inv]
    calc (x : G) * (z * t) = z * t * x * (z * t)⁻¹ * (z * t) := by rw [e]
      _ = z * t * x := by group
  obtain ⟨x, hxA, hx1, hxu⟩ := key
  have hxW : x ∈ W := (mem_inf.1 hxA).1
  obtain ⟨k, hk⟩ := (hW.to_le (zpowers_le.2 hxW)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hk
    exact hx1 hk
  have hord : orderOf x = 3 ^ k := by rwa [Nat.card_zpowers] at hk
  refine ⟨x ^ (3 ^ (k - 1)), W.pow_mem hxW _, ?_, ?_⟩
  · rw [orderOf_pow' x (pow_ne_zero _ (by norm_num)), hord,
      Nat.gcd_eq_right (pow_dvd_pow 3 (Nat.sub_le k 1)), Nat.pow_div (Nat.sub_le k 1) (by norm_num),
      show k - (k - 1) = 1 by omega, pow_one]
  · rcases hxu with h | h | h
    · exact Or.inl ((Commute.pow_left h _).eq)
    · exact Or.inr (Or.inl ((Commute.pow_left h _).eq))
    · exact Or.inr (Or.inr ((Commute.pow_left h _).eq))

theorem eq_bot_of_witness_klein [Finite G] {P S W : Subgroup G} (hWP : W ≤ P)
    (hW : IsPGroup 3 ↥W) (h729 : ∀ x ∈ W, x ^ 729 = 1) (hn : S ≤ normalizer (W : Set G))
    {z t : G} (hz : z ∈ S) (ht : t ∈ S) (hz2 : z ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hwit : ∀ y ∈ P, orderOf y = 3 →
      (y * z = z * y ∨ y * t = t * y ∨ y * (z * t) = (z * t) * y) →
      ∃ a ∈ S, ¬ (y * (a * y * a⁻¹)) ^ 729 = 1) : W = ⊥ := by
  by_contra hne
  obtain ⟨y, hyW, hy3, hyu⟩ := exists_orderOf_three_comm hW hne hn hz ht hz2 ht2
  obtain ⟨a, haS, ha⟩ := hwit y (hWP hyW) hy3 hyu
  exact ha (h729 _ (W.mul_mem hyW ((mem_normalizer_iff.1 (hn haS) y).1 hyW)))

end CFSG.Sporadic.Recognition.McLAS

end
