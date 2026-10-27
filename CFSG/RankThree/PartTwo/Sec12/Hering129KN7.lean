module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129KN7

theorem isPGroup_zpowers_of_pow_pow_eq_one {G : Type*} [Group G] {g : G} {p n : ℕ}
    (h : g ^ p ^ n = 1) : IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem exists_common_fixed_point {α : Type*} {p : ℕ} [Fact p.Prime] (hα : ¬ p ∣ Nat.card α)
    {σ₁ σ₂ : Equiv.Perm α} (h₁ : σ₁ ^ p = 1) (h₂ : σ₂ ^ p = 1) (h₁₂ : Commute σ₁ σ₂) :
    ∃ a, σ₁ a = a ∧ σ₂ a = a := by
  have hN : Subgroup.zpowers σ₁ ≤
      Subgroup.normalizer (Subgroup.zpowers σ₂ : Set (Equiv.Perm α)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_right h₁₂ i).eq).symm
  have hP : IsPGroup p ↥(Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂) :=
    IsPGroup.to_sup_of_normal_right'
      (isPGroup_zpowers_of_pow_pow_eq_one (n := 1) (by rwa [pow_one]))
      (isPGroup_zpowers_of_pow_pow_eq_one (n := 1) (by rwa [pow_one])) hN
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hα
  exact ⟨a, ha ⟨σ₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers σ₁)⟩,
    ha ⟨σ₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers σ₂)⟩⟩

end Hering129KN7

theorem exists_t_lift {H : Type} [Group H] [Finite H] {R : Subgroup H} [R.Normal]
    (hR : IsPGroup 2 R) {b c t₁ : H} (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hbc : b * c = c * b)
    (ht2 : t₁ ^ 2 ∈ R) (htb : b * t₁ * b⁻¹ * t₁⁻¹ ∈ R) (htc : t₁ * c * t₁⁻¹ * c ∈ R) :
    ∃ t : H, t₁⁻¹ * t ∈ R ∧ IsPGroup 2 (Subgroup.zpowers t) ∧ b * t = t * b ∧
      t * c * t⁻¹ = c⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hmem, hcoset⟩ : ∃ π : H →* H ⧸ R, (∀ x, x ∈ R ↔ π x = 1) ∧
      ∀ y, t₁⁻¹ * y ∈ R ↔ π y = π t₁ :=
    ⟨QuotientGroup.mk' R, fun x => (QuotientGroup.eq_one_iff x).symm,
      fun y => by rw [eq_comm]; exact QuotientGroup.eq.symm⟩
  have hτ2 : π t₁ * π t₁ = 1 := by rw [← map_mul, ← sq]; exact (hmem _).mp ht2
  have hτinv : (π t₁)⁻¹ = π t₁ := inv_eq_of_mul_eq_one_right hτ2
  have hbτ : π b * π t₁ = π t₁ * π b := by
    have h := (hmem _).mp htb
    simp only [map_mul, map_inv] at h
    rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  have hcτ : π c * π t₁ * π c = π t₁ := by
    have h := (hmem _).mp htc
    simp only [map_mul, map_inv] at h
    rw [hτinv] at h
    calc π c * π t₁ * π c = (π t₁)⁻¹ * (π t₁ * π c * π t₁ * π c) := by group
      _ = π t₁ := by rw [h, mul_one, hτinv]
  let Ω := {y : H // π y = π t₁}
  have hΩ : ¬ 3 ∣ Nat.card Ω := by
    have hcard : Nat.card Ω = Nat.card R :=
      Nat.card_congr
        { toFun := fun y => ⟨t₁⁻¹ * y, (hcoset y).mpr y.2⟩
          invFun := fun r => ⟨t₁ * r, by rw [map_mul, (hmem r).mp r.2, mul_one]⟩
          left_inv := fun y => Subtype.ext (mul_inv_cancel_left t₁ y)
          right_inv := fun r => Subtype.ext (inv_mul_cancel_left t₁ r) }
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hcard, hk]
    intro h
    have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  let σ₁ : Equiv.Perm Ω :=
    { toFun := fun y => ⟨b * y * b⁻¹, by
        rw [map_mul, map_mul, map_inv, y.2, hbτ, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨b⁻¹ * y * b, by
        rw [map_mul, map_mul, map_inv, y.2, mul_assoc, ← hbτ, inv_mul_cancel_left]⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  let σ₂ : Equiv.Perm Ω :=
    { toFun := fun y => ⟨c * y * c, by rw [map_mul, map_mul, y.2, hcτ]⟩
      invFun := fun y => ⟨c⁻¹ * y * c⁻¹, by
        rw [map_mul, map_mul, map_inv, y.2]
        calc (π c)⁻¹ * π t₁ * (π c)⁻¹ = (π c)⁻¹ * (π c * π t₁ * π c) * (π c)⁻¹ := by
              rw [hcτ]
          _ = π t₁ := by group⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  have hσ₁ : σ₁ ^ 3 = 1 := by
    rw [pow_three]
    refine Equiv.ext fun y => Subtype.ext ?_
    show b * (b * (b * (y : H) * b⁻¹) * b⁻¹) * b⁻¹ = y
    calc b * (b * (b * (y : H) * b⁻¹) * b⁻¹) * b⁻¹ = b * b * b * y * (b * b * b)⁻¹ := by
          group
      _ = y := by rw [← pow_three', hb3, one_mul, inv_one, mul_one]
  have hσ₂ : σ₂ ^ 3 = 1 := by
    rw [pow_three]
    refine Equiv.ext fun y => Subtype.ext ?_
    show c * (c * (c * (y : H) * c) * c) * c = y
    calc c * (c * (c * (y : H) * c) * c) * c = c * c * c * y * (c * c * c) := by
          simp only [mul_assoc]
      _ = y := by rw [← pow_three', hc3, one_mul, mul_one]
  have hcomm : Commute σ₁ σ₂ := by
    refine Equiv.ext fun y => Subtype.ext ?_
    show b * (c * (y : H) * c) * b⁻¹ = c * (b * y * b⁻¹) * c
    have hbc' : Commute b c := hbc
    calc b * (c * (y : H) * c) * b⁻¹ = b * c * y * (c * b⁻¹) := by group
      _ = c * b * y * (b⁻¹ * c) := by rw [hbc, ← hbc'.inv_left.eq]
      _ = c * (b * y * b⁻¹) * c := by group
  obtain ⟨y, hy₁, hy₂⟩ := Hering129KN7.exists_common_fixed_point hΩ hσ₁ hσ₂ hcomm
  have hyb : b * (y : H) * b⁻¹ = y := congrArg Subtype.val hy₁
  have hyc : c * (y : H) * c = y := congrArg Subtype.val hy₂
  refine ⟨y, (hcoset y).mpr y.2, ?_, mul_inv_eq_iff_eq_mul.mp hyb, ?_⟩
  · have hy2 : (y : H) ^ 2 ∈ R := by
      rw [hmem, map_pow, y.2, sq, hτ2]
    obtain ⟨k, hk⟩ := hR ⟨_, hy2⟩
    refine Hering129KN7.isPGroup_zpowers_of_pow_pow_eq_one (n := k + 1) ?_
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k from pow_succ' 2 k, pow_mul]
    simpa using congrArg Subtype.val hk
  · calc (y : H) * c * (y : H)⁻¹ = c⁻¹ * (c * y * c) * (y : H)⁻¹ := by group
      _ = c⁻¹ := by rw [hyc, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec12
