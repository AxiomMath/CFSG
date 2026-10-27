module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.ModD

variable {Γ ι U : Type*} [Group Γ] [CommGroup U]

structure LiftData (φ : Γ →* MulAut U) (π : Γ →* Equiv.Perm ι) (Z : Subgroup U) (s : ι → U) : Prop where
  sq : ∀ a : U, a * a = 1
  zfix : ∀ (g : Γ), ∀ ζ ∈ Z, φ g ζ = ζ
  equiv : ∀ (g : Γ) (i : ι), φ g (s i) = s (π g i)
  inj : ∀ i j : ι, s i * s j ∈ Z → i = j
  surj : ∀ m : U, m ∉ Z → ∃ i : ι, m * s i ∈ Z
  nz : ∀ i : ι, s i ∉ Z

namespace LiftData

variable {φ : Γ →* MulAut U} {π : Γ →* Equiv.Perm ι} {Z : Subgroup U} {s : ι → U}
  (d : LiftData φ π Z s)

include d

theorem D_inv {i j k : ι} (h : s i * s j * s k ∈ Z) (g : Γ) :
    s (π g i) * s (π g j) * s (π g k) = s i * s j * s k := by
  rw [← d.equiv g i, ← d.equiv g j, ← d.equiv g k, ← map_mul, ← map_mul]
  exact d.zfix g _ h

theorem D_mem {i j k : ι} (h : s i * s j * s k ∈ Z) (g : Γ) :
    s (π g i) * s (π g j) * s (π g k) ∈ Z := by
  rw [d.D_inv h g]
  exact h

theorem sum_unique {i j k k' : ι} (h : s i * s j * s k ∈ Z) (h' : s i * s j * s k' ∈ Z) : k = k' := by
  apply d.inj
  have e : s k * s k' = (s i * s j * s k) * (s i * s j * s k') := by
    calc s k * s k' = (s i * s i) * (s j * s j) * (s k * s k') := by
          rw [d.sq (s i), d.sq (s j)]
          simp
      _ = (s i * s j * s k) * (s i * s j * s k') := by ac_rfl
  rw [e]
  exact Z.mul_mem h h'

theorem exists_sum {i j : ι} (hij : i ≠ j) : ∃ k, s i * s j * s k ∈ Z := by
  apply d.surj
  intro h
  exact hij (d.inj i j h)

theorem sum_ne {i j k : ι} (h : s i * s j * s k ∈ Z) : k ≠ i ∧ k ≠ j := by
  constructor
  · intro hk
    subst hk
    apply d.nz j
    have e : s k * s j * s k = s j := by
      calc s k * s j * s k = (s k * s k) * s j := by ac_rfl
        _ = s j := by rw [d.sq, one_mul]
    rwa [e] at h
  · intro hk
    subst hk
    apply d.nz i
    have e : s i * s k * s k = s i := by rw [mul_assoc, d.sq, mul_one]
    rwa [e] at h

theorem assoc_sum {a b c d' e f : ι} (h1 : s a * s b * s c ∈ Z) (h2 : s c * s d' * s e ∈ Z)
    (h3 : s b * s d' * s f ∈ Z) : s a * s f * s e ∈ Z := by
  have eq : s a * s f * s e = (s a * s b * s c) * (s c * s d' * s e) * (s b * s d' * s f) := by
    calc s a * s f * s e = (s a * s f * s e) * ((s b * s b) * (s c * s c) * (s d' * s d')) := by
          rw [d.sq (s b), d.sq (s c), d.sq (s d')]
          simp
      _ = (s a * s b * s c) * (s c * s d' * s e) * (s b * s d' * s f) := by ac_rfl
  rw [eq]
  exact Z.mul_mem (Z.mul_mem h1 h2) h3

theorem forced_sum {a b c : ι} (hab : a ≠ b) (L : List Γ) (hL : ∀ g ∈ L, π g a = a ∧ π g b = b)
    (hfix : ∀ x : ι, (∀ g ∈ L, π g x = x) → x = a ∨ x = b ∨ x = c) : s a * s b * s c ∈ Z := by
  obtain ⟨k, hk⟩ := d.exists_sum hab
  have hkfix : ∀ g ∈ L, π g k = k := by
    intro g hg
    have h1 := d.D_mem hk g
    rw [(hL g hg).1, (hL g hg).2] at h1
    exact d.sum_unique h1 hk
  rcases hfix k hkfix with h | h | h
  · exact absurd h (d.sum_ne hk).1
  · exact absurd h (d.sum_ne hk).2
  · rw [← h]
    exact hk

theorem key_eq {z0 v w c₁ c₂ c₃ : ι} (hc1w : c₁ ≠ w) (h1 : s z0 * s v * s c₁ ∈ Z)
    (h2 : s v * s w * s c₂ ∈ Z) (h3 : s z0 * s c₂ * s c₃ ∈ Z) (g : Γ) (hg0 : π g z0 = z0)
    (hg1 : π g v = c₃) (hg2 : π g c₁ = c₂) :
    s c₁ * s w * s c₃ ∈ Z ∧ s c₁ * s w * s c₃ = s v * s w * s c₂ := by
  obtain ⟨c₃', h4⟩ := d.exists_sum hc1w
  have h5 : s z0 * s c₂ * s c₃' ∈ Z := d.assoc_sum h1 h4 h2
  have hc : c₃' = c₃ := d.sum_unique h5 h3
  rw [hc] at h4
  refine ⟨h4, ?_⟩
  have h6 := d.D_inv h1 g
  rw [hg0, hg1, hg2] at h6
  have e1 : (s z0 * s v * s c₁) * (s c₁ * s w * s c₃) = s z0 * s v * s w * s c₃ := by
    calc (s z0 * s v * s c₁) * (s c₁ * s w * s c₃)
        = (s z0 * s v * s w * s c₃) * (s c₁ * s c₁) := by ac_rfl
      _ = s z0 * s v * s w * s c₃ := by rw [d.sq, mul_one]
  have e2 : (s z0 * s c₃ * s c₂) * (s v * s w * s c₂) = s z0 * s v * s w * s c₃ := by
    calc (s z0 * s c₃ * s c₂) * (s v * s w * s c₂)
        = (s z0 * s v * s w * s c₃) * (s c₂ * s c₂) := by ac_rfl
      _ = s z0 * s v * s w * s c₃ := by rw [d.sq, mul_one]
  have e : (s z0 * s v * s c₁) * (s c₁ * s w * s c₃) = (s z0 * s v * s c₁) * (s v * s w * s c₂) := by
    rw [e1, ← h6, e2]
  exact mul_left_cancel e

theorem closure_of_bases (bases : List (ι × ι × ι)) (hbases : ∀ b ∈ bases, s b.1 * s b.2.1 = s b.2.2)
    (C : Set ι) (hwit : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ∃ h : Γ, ∃ b ∈ bases,
      π h b.1 = i ∧ π h b.2.1 = j ∧ π h b.2.2 ∈ C) :
    ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ∃ k ∈ C, s i * s j = s k := by
  intro i hi j hj hij
  obtain ⟨h, b, hb, h1, h2, h3⟩ := hwit i hi j hj hij
  refine ⟨π h b.2.2, h3, ?_⟩
  rw [← h1, ← h2, ← d.equiv h b.1, ← d.equiv h b.2.1, ← map_mul, hbases b hb, d.equiv]

end LiftData

end CFSG.Quasithin.ModD
