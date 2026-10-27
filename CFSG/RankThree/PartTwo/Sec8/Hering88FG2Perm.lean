module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88F

open scoped Pointwise

theorem exists_fixed_of_pow_three {g : Equiv.Perm (Fin 28)} (hg : g ^ 3 = 1) :
    ∃ p : Fin 28, g p = p := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup (Equiv.Perm (Fin 28)) := Subgroup.zpowers g with hZ
  have hp : IsPGroup 3 Z := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hg, one_zpow]
    rfl
  have hmod := hp.card_modEq_card_fixedPoints (α := Fin 28)
  by_contra hno'
  have hno : ∀ p : Fin 28, g p ≠ p := fun p hp => hno' ⟨p, hp⟩
  have hfix : Nat.card (MulAction.fixedPoints Z (Fin 28)) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨p, hp'⟩ => ?_⟩
    exact hno p (by simpa using hp' ⟨g, Subgroup.mem_zpowers g⟩)
  rw [hfix, Nat.card_eq_fintype_card, Fintype.card_fin] at hmod
  exact absurd hmod (by decide)

section TwoTransitive

variable {H : Subgroup (Equiv.Perm (Fin 28))}

theorem exists_mem_apply_zero (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q)
    (p : Fin 28) : ∃ h ∈ H, h 0 = p := by
  by_cases hp : p = 0
  · exact ⟨1, H.one_mem, by simp [hp]⟩
  · obtain ⟨h, hh, hh0, -⟩ := h2t p 0 hp
    exact ⟨h, hh, hh0⟩

theorem card_stabilizer_zero (hcard : Nat.card H = 6048)
    (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q) :
    Nat.card (MulAction.stabilizer H (0 : Fin 28)) = 216 := by
  haveI : MulAction.IsPretransitive H (Fin 28) := ⟨fun x y => by
    obtain ⟨h, hh, hx⟩ := exists_mem_apply_zero h2t x
    obtain ⟨k, hk, hy⟩ := exists_mem_apply_zero h2t y
    refine ⟨⟨k * h⁻¹, H.mul_mem hk (H.inv_mem hh)⟩, ?_⟩
    rw [← hx, ← hy]
    show (k * h⁻¹) (h 0) = k 0
    simp⟩
  have h1 := MulAction.index_stabilizer_of_transitive H (0 : Fin 28)
  have h2 := (MulAction.stabilizer H (0 : Fin 28)).card_mul_index
  rw [h1, hcard, Nat.card_eq_fintype_card (α := Fin 28), Fintype.card_fin] at h2
  omega

theorem card_stabilizer_pair (hcard : Nat.card H = 6048)
    (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q) :
    Nat.card (MulAction.stabilizer H ((0, 1) : Fin 28 × Fin 28)) = 8 := by
  have horb : MulAction.orbit H ((0, 1) : Fin 28 × Fin 28) =
      ↑(Finset.univ.filter fun pq : Fin 28 × Fin 28 => pq.1 ≠ pq.2) := by
    ext ⟨p, q⟩
    simp only [MulAction.mem_orbit_iff, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h, hh⟩, hpq⟩
      have h1 : h 0 = p := congrArg Prod.fst hpq
      have h2 : h 1 = q := congrArg Prod.snd hpq
      rw [← h1, ← h2]
      exact fun he => absurd (h.injective he) (by decide)
    · intro hpq
      obtain ⟨h, hh, h1, h2⟩ := h2t p q hpq
      exact ⟨⟨h, hh⟩, by
        show (h 0, h 1) = (p, q)
        rw [h1, h2]⟩
  have h1 := MulAction.index_stabilizer H ((0, 1) : Fin 28 × Fin 28)
  have h2 := (MulAction.stabilizer H ((0, 1) : Fin 28 × Fin 28)).card_mul_index
  rw [horb, Set.ncard_coe_finset] at h1
  have h756 : (Finset.univ.filter fun pq : Fin 28 × Fin 28 => pq.1 ≠ pq.2).card = 756 := by
    decide +kernel
  rw [h756] at h1
  rw [h1, hcard] at h2
  omega

theorem eq_one_of_fix_two (hcard : Nat.card H = 6048)
    (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q) {g : Equiv.Perm (Fin 28)}
    (hg : g ∈ H) (hg3 : g ^ 3 = 1) {p q : Fin 28} (hpq : p ≠ q) (hp : g p = p) (hq : g q = q) :
    g = 1 := by
  obtain ⟨h, hh, h0, h1⟩ := h2t p q hpq
  set S := MulAction.stabilizer H ((0, 1) : Fin 28 × Fin 28) with hS
  set g' : H := ⟨h⁻¹ * g * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hg) hh⟩ with hg'
  have hg'S : g' ∈ S := by
    rw [hS, MulAction.mem_stabilizer_iff]
    have e0 : (h⁻¹ * g * h) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, hp, Equiv.Perm.inv_eq_iff_eq]
      exact h0.symm
    have e1 : (h⁻¹ * g * h) 1 = 1 := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hq, Equiv.Perm.inv_eq_iff_eq]
      exact h1.symm
    show ((h⁻¹ * g * h) 0, (h⁻¹ * g * h) 1) = (0, 1)
    rw [e0, e1]
  have hord8 : orderOf (⟨g', hg'S⟩ : S) ∣ 8 := by
    rw [← card_stabilizer_pair hcard h2t]
    exact orderOf_dvd_natCard _
  have hord3 : orderOf (⟨g', hg'S⟩ : S) ∣ 3 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Subtype.ext
    apply Subtype.ext
    simp only [hg', Subgroup.coe_pow, OneMemClass.coe_one]
    have hc : (h⁻¹ * g * h) ^ 3 = h⁻¹ * g ^ 3 * h := by
      have := conj_pow (a := h⁻¹) (b := g) (i := 3)
      simpa only [inv_inv] using this
    rw [hc, hg3]
    group
  have h1' : orderOf (⟨g', hg'S⟩ : S) = 1 := by
    have := Nat.dvd_gcd hord8 hord3
    simpa using this
  have hone : (⟨g', hg'S⟩ : S) = 1 := orderOf_eq_one_iff.mp h1'
  have : h⁻¹ * g * h = 1 := congrArg (fun x : S => ((x : H) : Equiv.Perm (Fin 28))) hone
  calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem eq_one_of_fix_one (hcard : Nat.card H = 6048)
    (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q) {t : Equiv.Perm (Fin 28)}
    (ht : t ∈ H) (ht7 : t ^ 7 = 1) {p : Fin 28} (hp : t p = p) : t = 1 := by
  obtain ⟨h, hh, h0⟩ := exists_mem_apply_zero h2t p
  set S := MulAction.stabilizer H (0 : Fin 28) with hS
  set t' : H := ⟨h⁻¹ * t * h, H.mul_mem (H.mul_mem (H.inv_mem hh) ht) hh⟩ with ht'
  have ht'S : t' ∈ S := by
    rw [hS, MulAction.mem_stabilizer_iff]
    show (h⁻¹ * t * h) 0 = 0
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, hp, Equiv.Perm.inv_eq_iff_eq]
    exact h0.symm
  have hord216 : orderOf (⟨t', ht'S⟩ : S) ∣ 216 := by
    rw [← card_stabilizer_zero hcard h2t]
    exact orderOf_dvd_natCard _
  have hord7 : orderOf (⟨t', ht'S⟩ : S) ∣ 7 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Subtype.ext
    apply Subtype.ext
    simp only [ht', Subgroup.coe_pow, OneMemClass.coe_one]
    have hc : (h⁻¹ * t * h) ^ 7 = h⁻¹ * t ^ 7 * h := by
      have := conj_pow (a := h⁻¹) (b := t) (i := 7)
      simpa only [inv_inv] using this
    rw [hc, ht7]
    group
  have h1' : orderOf (⟨t', ht'S⟩ : S) = 1 := by
    have := Nat.dvd_gcd hord216 hord7
    simpa using this
  have hone : (⟨t', ht'S⟩ : S) = 1 := orderOf_eq_one_iff.mp h1'
  have : h⁻¹ * t * h = 1 := congrArg (fun x : S => ((x : H) : Equiv.Perm (Fin 28))) hone
  calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem no_comm_three_seven (hcard : Nat.card H = 6048)
    (h2t : ∀ p q : Fin 28, p ≠ q → ∃ h ∈ H, h 0 = p ∧ h 1 = q) {g t : Equiv.Perm (Fin 28)}
    (hg : g ∈ H) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (ht : t ∈ H) (ht7 : t ^ 7 = 1) (ht1 : t ≠ 1) :
    g * t ≠ t * g := by
  intro hcomm
  obtain ⟨p, hp⟩ := exists_fixed_of_pow_three hg3
  have htp : t p = p := by
    have hgt : g (t p) = t p := by
      have := congrArg (fun x : Equiv.Perm (Fin 28) => x p) hcomm
      simp only [Equiv.Perm.mul_apply, hp] at this
      exact this
    by_contra hne
    exact hg1 (eq_one_of_fix_two hcard h2t hg hg3 hne hgt hp)
  exact ht1 (eq_one_of_fix_one hcard h2t ht ht7 htp)

end TwoTransitive

end CFSG.RankThree.PartTwo.Sec8.Hering88F
