module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.RankThree.PartTwo

variable {P : Type*} [Group P]

@[expose] def commHom (hP : ∀ a b : P, a * b = b * a) (φ : MulAut P) : P →* P where
  toFun a := a⁻¹ * φ a
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (φ a * φ b) = a⁻¹ * (b⁻¹ * (φ a * φ b)) := by
          rw [hP b⁻¹ a⁻¹, mul_assoc]
      _ = a⁻¹ * (φ a * (b⁻¹ * φ b)) := by
          rw [← mul_assoc b⁻¹, hP b⁻¹ (φ a), mul_assoc]
      _ = a⁻¹ * φ a * (b⁻¹ * φ b) := by rw [mul_assoc]

theorem commHom_apply (hP : ∀ a b : P, a * b = b * a) (φ : MulAut P) (a : P) :
    commHom hP φ a = a⁻¹ * φ a := rfl

theorem ker_commHom (hP : ∀ a b : P, a * b = b * a) (φ : MulAut P) :
    (commHom hP φ).ker = fixedSubgroupOf φ := by
  ext a
  rw [MonoidHom.mem_ker, commHom_apply, mem_fixedSubgroupOf, inv_mul_eq_one, eq_comm]

theorem range_commHom (hP : ∀ a b : P, a * b = b * a) (φ : MulAut P) :
    (commHom hP φ).range = commOf φ := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.subset_closure ⟨a, rfl⟩
  · rw [commOf, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem card_eq_card_fixed_mul_card_commOf [Finite P] (hP : ∀ a b : P, a * b = b * a)
    (φ : MulAut P) : Nat.card P = Nat.card (fixedSubgroupOf φ) * Nat.card (commOf φ) := by
  rw [← ker_commHom hP, ← range_commHom hP, ← Subgroup.index_ker]
  exact (Subgroup.card_mul_index _).symm

theorem inv_of_mem_commOf (hP : ∀ a b : P, a * b = b * a) {φ : MulAut P}
    (hφ : ∀ a, φ (φ a) = a) {w : P} (hw : w ∈ commOf φ) : φ w = w⁻¹ := by
  rw [← range_commHom hP] at hw
  obtain ⟨a, rfl⟩ := hw
  rw [commHom_apply, map_mul, map_inv, hφ, mul_inv_rev, inv_inv]

theorem apply_apply_of_orderOf_eq_two {φ : MulAut P} (hφ : orderOf φ = 2) (a : P) :
    φ (φ a) = a := by
  have h2 : φ ^ 2 = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have h := congrArg (fun ψ : MulAut P => ψ a) h2
  simpa [pow_two, MulAut.mul_apply] using h

theorem eq_sq_of_exponent_three (hP3 : ∀ a : P, a ^ 3 = 1) (φ : MulAut P) (a : P) :
    a = (a * φ a * ((φ a)⁻¹ * a)) ^ 2 := by
  rw [mul_assoc, mul_inv_cancel_left, ← sq, ← pow_mul]
  calc a = a ^ 3 * a := by rw [hP3, one_mul]
    _ = a ^ (2 * 2) := by rw [← pow_succ]

theorem eq_of_fixed_eq_of_commOf_eq (hP : ∀ a b : P, a * b = b * a) (hP3 : ∀ a : P, a ^ 3 = 1)
    {φ ψ : MulAut P} (hφ : orderOf φ = 2) (hψ : orderOf ψ = 2)
    (hfix : fixedSubgroupOf φ = fixedSubgroupOf ψ) (hcomm : commOf φ = commOf ψ) : φ = ψ := by
  have hφφ := apply_apply_of_orderOf_eq_two hφ
  have hψψ := apply_apply_of_orderOf_eq_two hψ
  ext a
  have hbφ : a * φ a ∈ fixedSubgroupOf φ := by
    rw [mem_fixedSubgroupOf, map_mul, hφφ]
    exact hP _ _
  have hwφ : (φ a)⁻¹ * a ∈ commOf φ := by
    have h := (commOf φ).inv_mem (mem_commOf φ a)
    rwa [mul_inv_rev, inv_inv] at h
  have ha := eq_sq_of_exponent_three hP3 φ a
  have key : ∀ χ : MulAut P, χ (a * φ a) = a * φ a → χ ((φ a)⁻¹ * a) = ((φ a)⁻¹ * a)⁻¹ →
      χ a = (a * φ a * ((φ a)⁻¹ * a)⁻¹) ^ 2 := by
    intro χ h1 h2
    calc χ a = χ ((a * φ a * ((φ a)⁻¹ * a)) ^ 2) := by rw [← ha]
      _ = _ := by rw [map_pow, map_mul, h1, h2]
  rw [key φ ((mem_fixedSubgroupOf φ _).mp hbφ) (inv_of_mem_commOf hP hφφ hwφ),
    key ψ ((mem_fixedSubgroupOf ψ _).mp (hfix ▸ hbφ)) (inv_of_mem_commOf hP hψψ (hcomm ▸ hwφ))]

theorem card_eq_three_mul_card_fixed [Finite P] (hP : ∀ a b : P, a * b = b * a)
    {φ : MulAut P} (hφ : IsReflectionOn φ) :
    Nat.card P = 3 * Nat.card (fixedSubgroupOf φ) := by
  rw [card_eq_card_fixed_mul_card_commOf hP φ, hφ.2, mul_comm]

theorem card_eq_nine_mul_card_inf [Finite P] (hP : ∀ a b : P, a * b = b * a)
    {φ ψ : MulAut P} (hφ : IsReflectionOn φ) (hψ : IsReflectionOn ψ)
    (hne : fixedSubgroupOf φ ≠ fixedSubgroupOf ψ) :
    Nat.card P = 9 * Nat.card (fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ : Subgroup P) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφc := card_eq_three_mul_card_fixed hP hφ
  have hψc := card_eq_three_mul_card_fixed hP hψ
  have hnle : ¬ fixedSubgroupOf φ ≤ fixedSubgroupOf ψ := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by omega))
  let g := (commHom hP ψ).comp (fixedSubgroupOf φ).subtype
  have hgψ : ∀ y : fixedSubgroupOf φ, g y = 1 ↔ (y : P) ∈ fixedSubgroupOf ψ := fun y => by
    rw [← ker_commHom hP ψ, MonoidHom.mem_ker]
    rfl
  have hker : g.ker.map (fixedSubgroupOf φ).subtype =
      fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hgψ y).mp (MonoidHom.mem_ker.mp hy)⟩
    · rintro ⟨hxφ, hxψ⟩
      exact ⟨⟨x, hxφ⟩, MonoidHom.mem_ker.mpr ((hgψ ⟨x, hxφ⟩).mpr hxψ), rfl⟩
  have hle : g.range ≤ commOf ψ := by
    rintro _ ⟨y, rfl⟩
    rw [← range_commHom hP]
    exact ⟨_, rfl⟩
  have hrange : g.range = commOf ψ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hψ.2]
    have hne1 : g.range ≠ ⊥ := by
      intro hb
      apply hnle
      intro x hx
      have h1 : g ⟨x, hx⟩ ∈ g.range := ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      exact (hgψ ⟨x, hx⟩).mp h1
    have hdvd : Nat.card g.range ∣ 3 := by
      rw [← hψ.2]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne1
    · exact h3.ge
  have hcard : Nat.card (fixedSubgroupOf φ) =
      Nat.card (fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ : Subgroup P) * 3 := by
    rw [← hker, Subgroup.card_map_of_injective (fixedSubgroupOf φ).subtype_injective, ← hψ.2,
      ← hrange, ← Subgroup.index_ker]
    exact (Subgroup.card_mul_index _).symm
  rw [hφc, hcard]
  ring

end CFSG.RankThree.PartTwo.Sec21
