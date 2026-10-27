module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RepresentationTheory.SzMartineau

variable {G R : Type*} [Group G] [Ring R]

@[expose] def IsTwistedCocycle (φ ψ : G →* R) (Y : G → R) : Prop :=
  ∀ g h, Y (g * h) = φ g * Y h + Y g * ψ h

@[expose] def coboundary (φ ψ : G →* R) (X : R) (g : G) : R := φ g * X - X * ψ g

@[simp] theorem coboundary_apply (φ ψ : G →* R) (X : R) (g : G) :
    coboundary φ ψ X g = φ g * X - X * ψ g := rfl

theorem isTwistedCocycle_coboundary (φ ψ : G →* R) (X : R) :
    IsTwistedCocycle φ ψ (coboundary φ ψ X) := by
  intro g h
  simp only [coboundary_apply, map_mul]
  noncomm_ring

theorem IsTwistedCocycle.sub {φ ψ : G →* R} {Y Y' : G → R} (hY : IsTwistedCocycle φ ψ Y)
    (hY' : IsTwistedCocycle φ ψ Y') : IsTwistedCocycle φ ψ (Y - Y') := by
  intro g h
  simp only [Pi.sub_apply, hY g h, hY' g h]
  noncomm_ring

theorem IsTwistedCocycle.map_one {φ ψ : G →* R} {Y : G → R} (hY : IsTwistedCocycle φ ψ Y) :
    Y 1 = 0 := by
  have h : Y 1 = Y 1 + Y 1 := by simpa using hY 1 1
  have h' : Y 1 + Y 1 = Y 1 + 0 := by simpa using h.symm
  simpa using add_left_cancel h'

theorem IsTwistedCocycle.map_inv {φ ψ : G →* R} {Y : G → R} (hY : IsTwistedCocycle φ ψ Y)
    (g : G) : Y g⁻¹ = -(φ g⁻¹ * Y g * ψ g⁻¹) := by
  have h := hY g⁻¹ g
  rw [inv_mul_cancel, hY.map_one] at h
  have h' : Y g⁻¹ * ψ g = -(φ g⁻¹ * Y g) := eq_neg_of_add_eq_zero_right h.symm
  have hψ : ψ g * ψ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel]
    exact MonoidHom.map_one ψ
  calc Y g⁻¹ = Y g⁻¹ * (ψ g * ψ g⁻¹) := by rw [hψ, mul_one]
    _ = (Y g⁻¹ * ψ g) * ψ g⁻¹ := by rw [mul_assoc]
    _ = -(φ g⁻¹ * Y g) * ψ g⁻¹ := by rw [h']
    _ = -(φ g⁻¹ * Y g * ψ g⁻¹) := by rw [neg_mul]

theorem IsTwistedCocycle.eq_zero_of_le_closure {H : Subgroup G} {S : Set G} (hSH : S ⊆ H)
    (hH : H ≤ Subgroup.closure S) {φ ψ : ↥H →* R} {Y : ↥H → R} (hY : IsTwistedCocycle φ ψ Y)
    (hS : ∀ s (hs : s ∈ S), Y ⟨s, hSH hs⟩ = 0) (g : ↥H) : Y g = 0 := by
  have hcl : Subgroup.closure S ≤ H := (Subgroup.closure_le H).mpr hSH
  have h := Subgroup.closure_induction (p := fun x hx => Y ⟨x, hcl hx⟩ = 0)
    (fun x hx => by
      have h : (⟨x, hcl (Subgroup.subset_closure hx)⟩ : ↥H) = ⟨x, hSH hx⟩ :=
        Subtype.ext rfl
      rw [h]
      exact hS x hx)
    (by
      have h : (⟨1, hcl (Subgroup.closure S).one_mem⟩ : ↥H) = 1 := Subtype.ext rfl
      rw [h]
      exact hY.map_one)
    (fun x y hx hy ihx ihy => by
      have h : (⟨x * y, hcl ((Subgroup.closure S).mul_mem hx hy)⟩ : ↥H) =
          ⟨x, hcl hx⟩ * ⟨y, hcl hy⟩ := Subtype.ext rfl
      rw [h, hY, ihx, ihy, mul_zero, zero_mul, add_zero])
    (fun x hx ih => by
      have h : (⟨x⁻¹, hcl ((Subgroup.closure S).inv_mem hx)⟩ : ↥H) =
          (⟨x, hcl hx⟩)⁻¹ := Subtype.ext rfl
      rw [h, hY.map_inv, ih, mul_zero, zero_mul, neg_zero])
    (hH g.2)
  have hg : g = (⟨(g : G), hcl (hH g.2)⟩ : ↥H) := Subtype.ext rfl
  rw [hg]
  exact h

section Averaging

variable {H : Type*} [Group H] [Fintype H]

private lemma sum_expand {φ ψ : G →* R} {Y : G → R} (hY : IsTwistedCocycle φ ψ Y)
    (τ : H →* G) (h : H) :
    (∑ h' : H, Y (τ h') * ψ (τ h'⁻¹)) =
      ∑ h' : H, (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) *
        (ψ (τ h'⁻¹) * ψ (τ h⁻¹)) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun h' => Y (τ h') * ψ (τ h'⁻¹))]
  refine Finset.sum_congr rfl fun h' _ => ?_
  simp only [Equiv.coe_mulLeft, map_mul, mul_inv_rev]
  rw [hY (τ h) (τ h')]

private lemma sum_simplify {φ ψ : G →* R} {Y : G → R} (τ : H →* G) (h : H) :
    (∑ h' : H, (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) *
        (ψ (τ h'⁻¹) * ψ (τ h⁻¹))) =
      φ (τ h) * (∑ h' : H, Y (τ h') * ψ (τ h'⁻¹)) * ψ (τ h⁻¹) +
        Y (τ h) * (Fintype.card H : R) * ψ (τ h⁻¹) := by
  have hterm : ∀ h' : H,
      (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) *
          (ψ (τ h'⁻¹) * ψ (τ h⁻¹)) =
        φ (τ h) * (Y (τ h') * ψ (τ h'⁻¹)) * ψ (τ h⁻¹) +
          Y (τ h) * ψ (τ h⁻¹) := by
    intro h'
    have hψ : ψ (τ h') * ψ (τ h'⁻¹) = 1 := by
      rw [← map_mul, MonoidHom.map_inv τ h', mul_inv_cancel]
      exact MonoidHom.map_one ψ
    calc (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) *
          (ψ (τ h'⁻¹) * ψ (τ h⁻¹))
        = (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) * ψ (τ h'⁻¹) *
            ψ (τ h⁻¹) := by rw [mul_assoc]
      _ = ((φ (τ h) * Y (τ h')) * ψ (τ h'⁻¹) +
            (Y (τ h) * ψ (τ h')) * ψ (τ h'⁻¹)) * ψ (τ h⁻¹) := by rw [add_mul]
      _ = (φ (τ h) * Y (τ h') * ψ (τ h'⁻¹) +
            Y (τ h)) * ψ (τ h⁻¹) := by
            rw [show (φ (τ h) * Y (τ h')) * ψ (τ h'⁻¹) =
                  φ (τ h) * Y (τ h') * ψ (τ h'⁻¹) by rw [mul_assoc],
                show (Y (τ h) * ψ (τ h')) * ψ (τ h'⁻¹) = Y (τ h) by
                  rw [mul_assoc, hψ, mul_one]]
      _ = φ (τ h) * (Y (τ h') * ψ (τ h'⁻¹)) * ψ (τ h⁻¹) +
            Y (τ h) * ψ (τ h⁻¹) := by
            rw [add_mul, mul_assoc (φ (τ h)) (Y (τ h')) (ψ (τ h'⁻¹))]
  rw [Finset.sum_congr rfl (fun h' _ => hterm h')]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  rw [Nat.cast_comm, mul_assoc, ← Nat.cast_comm, ← mul_assoc]

private lemma cocycle_key {φ ψ : G →* R} {Y : G → R} (hY : IsTwistedCocycle φ ψ Y)
    (τ : H →* G) (h : H) :
    (Fintype.card H : R) * Y (τ h) =
      (∑ h' : H, Y (τ h') * ψ (τ h'⁻¹)) * ψ (τ h) -
        φ (τ h) * (∑ h' : H, Y (τ h') * ψ (τ h'⁻¹)) := by
  set S : R := ∑ h' : H, Y (τ h') * ψ (τ h'⁻¹) with hSdef
  have h1 : S = ∑ h' : H, (φ (τ h) * Y (τ h') + Y (τ h) * ψ (τ h')) *
      (ψ (τ h'⁻¹) * ψ (τ h⁻¹)) := by
    rw [hSdef]
    exact sum_expand hY τ h
  have h2 : S = φ (τ h) * S * ψ (τ h⁻¹) +
      Y (τ h) * (Fintype.card H : R) * ψ (τ h⁻¹) := by
    conv_lhs => rw [h1]
    rw [hSdef]
    exact sum_simplify τ h
  have hRB : ψ (τ h⁻¹) * ψ (τ h) = 1 := by
    rw [← map_mul, ← map_mul τ h⁻¹ h, inv_mul_cancel, MonoidHom.map_one τ]
    exact MonoidHom.map_one ψ
  have hmul : S * ψ (τ h) = φ (τ h) * S + Y (τ h) * (Fintype.card H : R) := by
    calc S * ψ (τ h)
        = (φ (τ h) * S * ψ (τ h⁻¹) +
            Y (τ h) * (Fintype.card H : R) * ψ (τ h⁻¹)) * ψ (τ h) :=
            congrArg (· * ψ (τ h)) h2
      _ = (φ (τ h) * S * ψ (τ h⁻¹)) * ψ (τ h) +
            (Y (τ h) * (Fintype.card H : R) * ψ (τ h⁻¹)) * ψ (τ h) := by rw [add_mul]
      _ = (φ (τ h) * S) * (ψ (τ h⁻¹) * ψ (τ h)) +
            (Y (τ h) * (Fintype.card H : R)) * (ψ (τ h⁻¹) * ψ (τ h)) := by
            rw [mul_assoc (φ (τ h) * S) (ψ (τ h⁻¹)) (ψ (τ h)),
                mul_assoc (Y (τ h) * (Fintype.card H : R)) (ψ (τ h⁻¹)) (ψ (τ h))]
      _ = φ (τ h) * S + Y (τ h) * (Fintype.card H : R) := by
            rw [hRB, mul_one, mul_one]
  have h3 : S * ψ (τ h) - φ (τ h) * S = Y (τ h) * (Fintype.card H : R) := by
    rw [hmul, add_sub_cancel_left]
  have h4 : Y (τ h) * (Fintype.card H : R) = (Fintype.card H : R) * Y (τ h) :=
    (Nat.cast_comm _ _).symm
  exact (h3.trans h4).symm

private lemma coboundary_average {φ ψ : G →* R} {Y : G → R} (τ : H →* G) (h : H)
    (u : Rˣ) (hu : (u : R) = (Fintype.card H : R)) (S : R)
    (hkey : (Fintype.card H : R) * Y (τ h) = S * ψ (τ h) - φ (τ h) * S) :
    coboundary φ ψ (-(↑u⁻¹ * S)) (τ h) = Y (τ h) := by
  have hkeyu : (↑u : R) * Y (τ h) = S * ψ (τ h) - φ (τ h) * S := by
    rw [hu]
    exact hkey
  have hYu : Y (τ h) = (↑u⁻¹ : R) * (S * ψ (τ h) - φ (τ h) * S) := by
    calc Y (τ h) = (↑u⁻¹ : R) * ((↑u : R) * Y (τ h)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (↑u⁻¹ : R) * (S * ψ (τ h) - φ (τ h) * S) := by rw [hkeyu]
  have hcomm : ∀ x : R, (↑u⁻¹ : R) * x = x * ↑u⁻¹ := by
    intro x
    have hcu : Commute (↑u : R) x := by
      rw [hu]
      exact Nat.cast_commute _ _
    exact Commute.units_inv_left hcu
  have hcob : coboundary φ ψ (-(↑u⁻¹ * S)) (τ h) =
      (↑u⁻¹ : R) * (S * ψ (τ h) - φ (τ h) * S) := by
    rw [coboundary_apply]
    calc φ (τ h) * (-(↑u⁻¹ * S)) - (-(↑u⁻¹ * S)) * ψ (τ h)
        = -(φ (τ h) * (↑u⁻¹ * S)) + (↑u⁻¹ * S) * ψ (τ h) := by noncomm_ring
      _ = -(↑u⁻¹ * (φ (τ h) * S)) + ↑u⁻¹ * (S * ψ (τ h)) := by
            rw [← mul_assoc (φ (τ h)) (↑u⁻¹) S, ← hcomm (φ (τ h)),
                mul_assoc (↑u⁻¹) (φ (τ h)) S, mul_assoc (↑u⁻¹) S (ψ (τ h))]
      _ = ↑u⁻¹ * (S * ψ (τ h) - φ (τ h) * S) := by
            rw [← mul_neg, ← mul_add, neg_add_eq_sub]
  rw [hYu, hcob]

end Averaging

theorem IsTwistedCocycle.exists_eq_coboundary_comp {φ ψ : G →* R} {Y : G → R}
    (hY : IsTwistedCocycle φ ψ Y) {H : Type*} [Group H] [Fintype H] (τ : H →* G)
    (hH : IsUnit (Fintype.card H : R)) :
    ∃ X : R, ∀ h : H, Y (τ h) = coboundary φ ψ X (τ h) := by
  classical
  obtain ⟨u, hu⟩ := hH
  refine ⟨-(↑u⁻¹ * (∑ h' : H, Y (τ h') * ψ (τ h'⁻¹))), fun h => ?_⟩
  exact (coboundary_average τ h u hu _ (cocycle_key hY τ h)).symm

end CFSG.RepresentationTheory.SzMartineau
