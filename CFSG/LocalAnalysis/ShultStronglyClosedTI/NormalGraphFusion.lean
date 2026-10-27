module

public import CFSG.Assembly.OrderReductions.InvolutionFusion

public section

namespace CFSG.ShultStronglyClosedTI.NormalGraph

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.InvolutionFusion

variable {G : Type*} [Group G]

@[expose] def graph (D : Set G) (horder : ∀ x ∈ D, orderOf x = 2) : SimpleGraph D :=
  (commutingGraph G).comap (fun x => (⟨x, horder x x.property⟩ : Involution G))

theorem reachable_of_commute (D : Set G) (horder : ∀ x ∈ D, orderOf x = 2)
    (x y : D) (hcomm : Commute (x : G) (y : G)) : (graph D horder).Reachable x y := by
  by_cases hxy : x = y
  · exact hxy ▸ SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨?_, hcomm⟩
    intro h
    exact hxy (Subtype.ext (congrArg (fun t : Involution G => (t : G)) h))

theorem rotation_conjugates_reflection (t r : G)
    (hinverts : (MulAut.conj t) r = r⁻¹) (k : ℕ) :
    (MulAut.conj (r ^ k)) t = r ^ (k + k) * t := by
  have hmoves : t * (r ^ k)⁻¹ = r ^ k * t := by
    have hfix : (MulAut.conj t) ((r ^ k)⁻¹) = r ^ k := by
      rw [map_inv, map_pow, hinverts, inv_pow, inv_inv]
    have h := congrArg (fun x : G => x * t) hfix
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h
  rw [MulAut.conj_apply, mul_assoc, hmoves, ← mul_assoc, ← pow_add]

variable [Finite G]

theorem reachable_of_even_product_order (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (x y : D) (heven : Even (orderOf ((x : G) * y))) :
    (graph D horder).Reachable x y := by
  let first : Involution G := ⟨x, horder x x.property⟩
  let second : Involution G := ⟨y, horder y y.property⟩
  let r : G := (x : G) * y
  let m := orderOf r / 2
  let v := r ^ m
  have hvorder : orderOf v = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos r)) heven.two_dvd
  have hfirstFix : (MulAut.conj (x : G)) v = v := by
    change (MulAut.conj first.val) ((first.val * second.val) ^ m) = v
    rw [product_power_conjugate_inv]
    exact inv_eq_self_of_orderOf_eq_two hvorder
  have hxv : Commute (x : G) v := by
    change (x : G) * v = v * x
    have h := congrArg (fun w : G => w * x) hfirstFix
    exact (by simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h)
  have hrv : Commute r v := (Commute.refl r).pow_right m
  have hyr : (y : G) = (x : G) * r := by
    dsimp only [r]
    have hxpow := involution_mul_self first
    change (x : G) * x = 1 at hxpow
    rw [← mul_assoc, hxpow, one_mul]
  have hyv : Commute (y : G) v := by
    rw [hyr]
    exact hxv.mul_left hrv
  have hyflip : (MulAut.conj (y : G)) r = r⁻¹ := by
    have hxinv : (x : G)⁻¹ = x := inv_eq_self_of_orderOf_eq_two first.property
    dsimp only [r]
    rw [MulAut.conj_apply, mul_inv_rev, hxinv, mul_assoc, mul_inv_cancel_right]
    have hyinv : (y : G)⁻¹ = y := inv_eq_self_of_orderOf_eq_two second.property
    rw [hyinv]
  have hxflip : (MulAut.conj (x : G)) r = r⁻¹ := product_conjugate_inv first second
  have hrsecond : r * y = (x : G) := by
    dsimp only [r]
    have hypow := involution_mul_self second
    change (y : G) * y = 1 at hypow
    rw [mul_assoc, hypow, mul_one]
  let reflection := v * (y : G)
  have hreflection : reflection ∈ D := by
    rcases Nat.even_or_odd m with hm | hm
    · obtain ⟨k, hk⟩ := hm
      have heq : reflection = (MulAut.conj (r ^ k)) (y : G) := by
        rw [rotation_conjugates_reflection _ _ hyflip]
        change r ^ m * (y : G) = r ^ (k + k) * y
        rw [hk]
      rw [heq]
      exact hconj y y.property _
    · obtain ⟨k, hk⟩ := hm
      have heq : reflection = (MulAut.conj (r ^ k)) (x : G) := by
        rw [rotation_conjugates_reflection _ _ hxflip]
        change r ^ m * (y : G) = r ^ (k + k) * x
        rw [show m = k + k + 1 from by omega, pow_succ, mul_assoc, hrsecond]
      rw [heq]
      exact hconj x x.property _
  have hreflectionNe : reflection ≠ (y : G) := by
    intro h
    have hvone : v = 1 := mul_right_cancel (h.trans (one_mul (y : G)).symm)
    simp [hvone] at hvorder
  have hreflectionComm : Commute reflection (y : G) :=
    hyv.symm.mul_left (Commute.refl (y : G))
  have hvD : v ∈ D := by
    have h := hproduct reflection hreflection y y.property hreflectionNe hreflectionComm
    have hyeq := involution_mul_self second
    change (y : G) * y = 1 at hyeq
    simpa only [reflection, mul_assoc, hyeq, mul_one] using h
  exact (reachable_of_commute D horder x ⟨v, hvD⟩ hxv).trans
    (reachable_of_commute D horder y ⟨v, hvD⟩ hyv).symm

theorem odd_product_order_of_not_reachable (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (x y : D) (hnot : ¬ (graph D horder).Reachable x y) :
    Odd (orderOf ((x : G) * y)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact hnot (reachable_of_even_product_order D horder hconj hproduct x y heven)

theorem isConj_of_not_reachable (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (x y : D) (hnot : ¬ (graph D horder).Reachable x y) : IsConj (x : G) (y : G) := by
  let first : Involution G := ⟨x, horder x x.property⟩
  let second : Involution G := ⟨y, horder y y.property⟩
  obtain ⟨g, hg⟩ := conjugate_of_odd_product_order first second
    (odd_product_order_of_not_reachable D horder hconj hproduct x y hnot)
  apply isConj_iff.mpr
  exact ⟨g, congrArg (fun t : Involution G => (t : G)) hg⟩

theorem conjugacy_transitive (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected) (x y : D) :
    IsConj (x : G) (y : G) := by
  by_cases hreach : (graph D horder).Reachable x y
  · have houtside : ∃ z : D, ¬ (graph D horder).Reachable x z := by
      by_contra hnone
      push Not at hnone
      exact hdisconnected (fun a b => (hnone a).symm.trans (hnone b))
    obtain ⟨z, hxz⟩ := houtside
    have hyz : ¬ (graph D horder).Reachable y z := fun hyz => hxz (hreach.trans hyz)
    exact (isConj_of_not_reachable D horder hconj hproduct x z hxz).trans
      (isConj_of_not_reachable D horder hconj hproduct y z hyz).symm
  · exact isConj_of_not_reachable D horder hconj hproduct x y hreach

theorem eq_conjugacy_class (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected) (z : D) :
    D = conjugatesOf (z : G) := by
  ext x
  constructor
  · intro hx
    exact conjugacy_transitive D horder hconj hproduct hdisconnected z ⟨x, hx⟩
  · intro hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    exact hconj z z.property g

end CFSG.ShultStronglyClosedTI.NormalGraph
