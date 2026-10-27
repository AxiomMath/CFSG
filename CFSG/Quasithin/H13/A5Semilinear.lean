module

public import CFSG.Quasithin.H13.A5LNat

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem card_fixV_sq_of_semilinear (hV : ∀ w : V, w ^ 2 = 1) (θ : V →* V) (v : MulAut V)
    (hv2 : v * v = 1) (hθ : ∀ w : V, v (θ w) = θ (v w) * v w) :
    Nat.card (fixV (Subgroup.zpowers v)) ^ 2 = Nat.card V := by
  set C := fixV (Subgroup.zpowers v) with hC
  have hmem : ∀ w : V, w ∈ C ↔ v w = w := fun w => mem_fixV_zpowers_iff
  have hvv : ∀ w : V, v (v w) = w := by
    intro w
    have := congrArg (fun f : MulAut V => f w) hv2
    simpa [MulAut.mul_apply] using this
  have hsq : ∀ w : V, w * w = 1 := fun w => by rw [← pow_two]; exact hV w
  have hinv : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hsq w)
  have hkey : ∀ u : V, u ∈ C → θ u ∈ C → u = 1 := by
    intro u hu hθu
    have h1 : v (θ u) = θ u := (hmem _).mp hθu
    rw [hθ, (hmem u).mp hu] at h1
    have h2 : θ u * u = θ u * 1 := by rw [mul_one]; exact h1
    exact mul_left_cancel h2
  let f : ↥C × ↥C → V := fun p => (p.1 : V) * θ (p.2 : V)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : V) * (a' : V)⁻¹ = θ ((b' : V) * (b : V)⁻¹) := by
      have h' : (a : V) * θ (b : V) = (a' : V) * θ (b' : V) := h
      rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_right_comm, mul_inv_eq_iff_eq_mul, h',
        mul_comm]
    have hu : (b' : V) * (b : V)⁻¹ ∈ C := C.mul_mem b'.2 (C.inv_mem b.2)
    have hθu : θ ((b' : V) * (b : V)⁻¹) ∈ C := by
      rw [← h1]
      exact C.mul_mem a.2 (C.inv_mem a'.2)
    have h2 := hkey _ hu hθu
    have hb : (b : V) = (b' : V) := by
      have := mul_inv_eq_one.mp h2
      exact this.symm
    rw [h2, map_one] at h1
    have ha : (a : V) = (a' : V) := mul_inv_eq_one.mp h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    have hv : ∀ x : V, x * v x ∈ C := fun x => by
      rw [hmem, map_mul, hvv, mul_comm]
    have hw : ∀ x : V, v x = (θ x * v (θ x)) * θ (x * v x) := by
      intro x
      rw [hθ x, map_mul]
      calc v x = (θ x * θ x) * (θ (v x) * θ (v x)) * v x := by rw [hsq, hsq, one_mul, one_mul]
        _ = θ x * (θ (v x) * v x) * (θ x * θ (v x)) := by
            simp only [mul_comm, mul_left_comm]
    intro y
    refine ⟨(⟨θ (v y) * v (θ (v y)), hv (θ (v y))⟩, ⟨v y * v (v y), hv (v y)⟩), ?_⟩
    show θ (v y) * v (θ (v y)) * θ (v y * v (v y)) = y
    rw [← hw (v y), hvv]
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  rw [pow_two, hcard]

theorem index_fixV_of_semilinear (hV : ∀ w : V, w ^ 2 = 1) (θ : V →* V) (v : MulAut V)
    (hv2 : v * v = 1) (hθ : ∀ w : V, v (θ w) = θ (v w) * v w) {k : ℕ}
    (hcard : Nat.card V = 2 ^ (2 * k)) : (fixV (Subgroup.zpowers v)).index = 2 ^ k := by
  have h1 := card_fixV_sq_of_semilinear hV θ v hv2 hθ
  rw [hcard, pow_mul'] at h1
  have hC : Nat.card (fixV (Subgroup.zpowers v)) = 2 ^ k :=
    Nat.pow_left_injective (by norm_num) h1
  have h3 := (fixV (Subgroup.zpowers v)).card_mul_index
  rw [hC, hcard] at h3
  have h4 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h3

end CFSG.Quasithin.H13.A5
