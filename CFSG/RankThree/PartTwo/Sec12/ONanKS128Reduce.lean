module

public import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

section Cocycle

variable {X : Type} [Group X]

@[expose] def cocycle (u : X) (σ : MulAut X) : X := σ u * u⁻¹

theorem cocycle_mul (u : X) (σ τ : MulAut X) :
    cocycle u (σ * τ) = σ (cocycle u τ) * cocycle u σ := by
  simp only [cocycle, MulAut.mul_apply, map_mul, map_inv]
  group

theorem cocycle_one (u : X) : cocycle u (1 : MulAut X) = 1 := by
  simp [cocycle]

def cocycleSubgroup (Y : Subgroup (MulAut X)) (W : Subgroup X)
    (hW : ∀ σ ∈ Y, ∀ w ∈ W, σ w = w) (u : X) : Subgroup (MulAut X) where
  carrier := {σ | σ ∈ Y ∧ cocycle u σ ∈ W}
  mul_mem' := by
    rintro σ τ ⟨hσ, hσW⟩ ⟨hτ, hτW⟩
    refine ⟨mul_mem hσ hτ, ?_⟩
    rw [cocycle_mul, hW σ hσ _ hτW]
    exact mul_mem hτW hσW
  one_mem' := ⟨one_mem Y, by rw [cocycle_one]; exact one_mem W⟩
  inv_mem' := by
    rintro σ ⟨hσ, hσW⟩
    refine ⟨inv_mem hσ, ?_⟩
    have h1 : σ (cocycle u σ⁻¹) * cocycle u σ = 1 := by
      rw [← cocycle_mul, mul_inv_cancel, cocycle_one]
    have h2 : σ (cocycle u σ⁻¹) = (cocycle u σ)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : cocycle u σ⁻¹ = σ⁻¹ ((cocycle u σ)⁻¹) := by
      rw [← h2]
      simp
    rw [h3, hW σ⁻¹ (inv_mem hσ) _ (inv_mem hσW)]
    exact inv_mem hσW

end Cocycle

section Generation

variable {G : Type} [Group G]

theorem zpowers_sup_zpowers_eq {Y : Subgroup G} (hY : Nat.card Y = 9) {a σ : G}
    (ha : orderOf a = 3) (haY : a ∈ Y) (hσ : σ ∈ Y) (hσa : σ ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers σ = Y := by
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  set A := Subgroup.zpowers a with hA
  set B := A ⊔ Subgroup.zpowers σ with hB
  have hBY : B ≤ Y := sup_le (Subgroup.zpowers_le.2 haY) (Subgroup.zpowers_le.2 hσ)
  have hAB : A ≤ B := le_sup_left
  have hA3 : Nat.card A = 3 := by rw [hA, Nat.card_zpowers, ha]
  have hBdvd : Nat.card B ∣ 9 := hY ▸ Subgroup.card_dvd_of_le hBY
  have hAdvd : 3 ∣ Nat.card B := hA3 ▸ Subgroup.card_dvd_of_le hAB
  have hfinB : Finite B :=
    Finite.of_injective (Subgroup.inclusion hBY) (Subgroup.inclusion_injective hBY)
  have hB9 : Nat.card B = 9 := by
    have hle : Nat.card B ≤ 9 := Nat.le_of_dvd (by norm_num) hBdvd
    have hge : 3 ≤ Nat.card B := Nat.le_of_dvd Nat.card_pos hAdvd
    obtain ⟨k, hk⟩ := hAdvd
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl
    · exfalso
      have hAB' : A = B := Subgroup.eq_of_le_of_card_ge hAB (by omega)
      exact hσa (hAB' ▸ (le_sup_right : Subgroup.zpowers σ ≤ B) (Subgroup.mem_zpowers σ))
    · exfalso
      rw [hk] at hBdvd
      norm_num at hBdvd
    · omega
  exact Subgroup.eq_of_le_of_card_ge hBY (by omega)

end Generation

section Main

variable {X : Type} [Group X]

theorem zmod_three_cube (a : ZMod 3) (h : a * (a * a) = 1) : a = 1 := by
  revert a
  decide

theorem fixes_center (hZ3 : Nat.card (Subgroup.center X) = 3) {σ : MulAut X} (hσ : σ ^ 3 = 1)
    {z : X} (hz : z ∈ Subgroup.center X) : σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ w ∈ Subgroup.center X, σ w ∈ Subgroup.center X := by
    intro w hw
    rw [Subgroup.mem_center_iff] at hw ⊢
    intro y
    apply σ.symm.injective
    simp only [map_mul, MulEquiv.symm_apply_apply]
    exact hw (σ.symm y)
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    simpa using congrArg Subtype.val this
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hfin : Finite (Subgroup.center X) := Nat.finite_of_card_ne_zero (by omega)
  have hZeq : Subgroup.zpowers z = Subgroup.center X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) (by
      rw [Nat.card_zpowers, hord, hZ3])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (by rw [hZeq]; exact hmem z hz : σ z ∈ Subgroup.zpowers z)
  have h3 : σ (σ (σ z)) = z := by
    have := congrArg (fun τ : MulAut X => τ z) hσ
    simpa [pow_succ, MulAut.mul_apply] using this
  have hσk : ∀ m : ℤ, σ (z ^ m) = z ^ (k * m) := by
    intro m
    rw [map_zpow, ← hk, ← zpow_mul]
  have h4 : z ^ (k * (k * k)) = z ^ (1 : ℤ) := by
    have e1 : σ (σ (σ z)) = z ^ (k * (k * k)) := by
      rw [← hk, hσk, hσk]
    rw [← e1, h3, zpow_one]
  rw [zpow_eq_zpow_iff_modEq, hord] at h4
  have h5 := (ZMod.intCast_eq_intCast_iff _ _ 3).2 h4
  have h6 : (k : ZMod 3) = 1 := by
    apply zmod_three_cube
    simpa using h5
  have h7 : k ≡ 1 [ZMOD ((3 : ℕ) : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff k 1 3).1 (by simpa using h6)
  have h8 : z ^ k = z ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, hord]
    exact h7
  rw [← hk, h8, zpow_one]

theorem orderOf_conj_eq_three {x : X} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X) :
    orderOf (MulAut.conj x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxne : MulAut.conj x ≠ 1 := fun h => hxZ (by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun σ : MulAut X => σ y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group)
  exact orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hxne

theorem exists_not_mem_zpowers_conj {x : X} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X)
    {Y : Subgroup (MulAut X)} (hY9 : Nat.card Y = 9) :
    ∃ σ ∈ Y, σ ∉ Subgroup.zpowers (MulAut.conj x) := by
  by_contra h
  push Not at h
  have hle : Y ≤ Subgroup.zpowers (MulAut.conj x) := fun σ hσ => h σ hσ
  have hcard : Nat.card (Subgroup.zpowers (MulAut.conj x)) = 3 := by
    rw [Nat.card_zpowers, orderOf_conj_eq_three hx3 hxZ]
  have hfin : Finite (Subgroup.zpowers (MulAut.conj x)) :=
    Nat.finite_of_card_ne_zero (by omega)
  have := Subgroup.card_le_of_le hle
  omega

theorem move_of_one_generator {x : X} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X)
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    {Y : Subgroup (MulAut X)} (hY3 : ∀ σ ∈ Y, σ ^ 3 = 1) (hY9 : Nat.card Y = 9)
    (hxY : MulAut.conj x ∈ Y) (hfix : ∀ σ ∈ Y, σ x = x)
    {σ₀ : MulAut X} (hσ₀ : σ₀ ∈ Y) (hσ₀A : σ₀ ∉ Subgroup.zpowers (MulAut.conj x))
    {u : X} (h1 : u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center X)
    (h3 : σ₀ u * u⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center X)
    (h4 : σ₀ u * u⁻¹ ∉ Subgroup.center X) :
    (∀ σ ∈ Y, σ u * u⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center X) ∧
      ∀ σ ∈ Y, σ ∉ Subgroup.zpowers (MulAut.conj x) → σ u * u⁻¹ ∉ Subgroup.center X := by
  have hord : orderOf (MulAut.conj x) = 3 := orderOf_conj_eq_three hx3 hxZ
  have hZfix : ∀ σ ∈ Y, ∀ z ∈ Subgroup.center X, σ z = z :=
    fun σ hσ z hz => fixes_center hZ3 (hY3 σ hσ) hz
  have hHfix : ∀ σ ∈ Y, ∀ w ∈ Subgroup.zpowers x ⊔ Subgroup.center X, σ w = w := by
    intro σ hσ w hw
    have hle : Subgroup.zpowers x ⊔ Subgroup.center X ≤
        MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hfix σ hσ
      · intro z hz
        exact hZfix σ hσ z hz
    exact hle hw
  have hc : cocycle u (MulAut.conj x) = (u * x * u⁻¹ * x⁻¹)⁻¹ := by
    simp only [cocycle, MulAut.conj_apply]
    group
  have hcZ : cocycle u (MulAut.conj x) ∈ Subgroup.center X := by
    rw [hc]
    exact inv_mem h1
  have hcH : cocycle u (MulAut.conj x) ∈ Subgroup.zpowers x ⊔ Subgroup.center X :=
    Subgroup.mem_sup_right hcZ
  constructor
  · have hgen : Subgroup.zpowers (MulAut.conj x) ⊔ Subgroup.zpowers σ₀ ≤
        cocycleSubgroup Y (Subgroup.zpowers x ⊔ Subgroup.center X) hHfix u :=
      sup_le (Subgroup.zpowers_le.2 ⟨hxY, hcH⟩) (Subgroup.zpowers_le.2 ⟨hσ₀, h3⟩)
    rw [zpowers_sup_zpowers_eq hY9 hord hxY hσ₀ hσ₀A] at hgen
    exact fun σ hσ => (hgen hσ).2
  · intro σ hσ hσA hσZ
    have hgen : Subgroup.zpowers (MulAut.conj x) ⊔ Subgroup.zpowers σ ≤
        cocycleSubgroup Y (Subgroup.center X) hZfix u :=
      sup_le (Subgroup.zpowers_le.2 ⟨hxY, hcZ⟩) (Subgroup.zpowers_le.2 ⟨hσ, hσZ⟩)
    rw [zpowers_sup_zpowers_eq hY9 hord hxY hσ hσA] at hgen
    exact h4 (hgen hσ₀).2

end Main

end CFSG.RankThree.PartTwo.Sec12.KS128Move
