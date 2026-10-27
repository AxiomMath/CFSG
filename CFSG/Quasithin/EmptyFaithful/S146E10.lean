module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin

open scoped Pointwise

section Counting

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_zpowers_of_sq_eq_one {a z : X} (ha : a ^ 2 = 1) (hz : z ∈ Subgroup.zpowers a) :
    z = 1 ∨ z = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2 : a ^ (2 : ℤ) = 1 := by exact_mod_cast ha
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_sup_zpowers_iff {A : Subgroup X} {a x : X} (ha : a ^ 2 = 1)
    (hcomm : ∀ y ∈ A, y * a = a * y) : x ∈ A ⊔ Subgroup.zpowers a ↔ x ∈ A ∨ x * a⁻¹ ∈ A := by
  have hc : ∀ y ∈ A, ∀ z ∈ Subgroup.zpowers a, y * z = z * y := by
    intro y hy z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right (show Commute y a from hcomm y hy) n)).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A (Subgroup.zpowers a) hc
  constructor
  · intro hx
    have hx' : x ∈ (A : Set X) * (Subgroup.zpowers a : Set X) := by rw [← hset]; exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx'
    rcases mem_zpowers_of_sq_eq_one ha hz with rfl | rfl
    · left; simpa using hy
    · right; simpa using hy
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : x = (x * a⁻¹) * a := by group
      rw [this]
      exact (A ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))

theorem card_sup_zpowers_eq {A : Subgroup X} {a : X} (ha : a ^ 2 = 1)
    (hcomm : ∀ y ∈ A, y * a = a * y) (haA : a ∉ A) :
    Nat.card ↥(A ⊔ Subgroup.zpowers a) = 2 * Nat.card A := by
  have hc : ∀ y ∈ A, ∀ z ∈ Subgroup.zpowers a, y * z = z * y := by
    intro y hy z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right (show Commute y a from hcomm y hy) n)).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A (Subgroup.zpowers a) hc
  have ha1 : a ≠ 1 := fun h => haA (h ▸ A.one_mem)
  have hord : orderOf a = 2 := orderOf_eq_prime (by simpa using ha) ha1
  have h2 : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, hord]
  have hinf : A ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzA, hz⟩
    rcases mem_zpowers_of_sq_eq_one ha hz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hzA haA
  rw [hinf, h2, Subgroup.card_bot, mul_one] at hcard
  rw [hcard, mul_comm]

theorem card_sup_closure_three {Uall Z UX : Subgroup X}
    (hcomm : ∀ x ∈ Uall, ∀ y ∈ Uall, x * y = y * x) (hsq : ∀ x ∈ Uall, x ^ 2 = 1)
    (hZU : Z ≤ UX) (hXU : UX ≤ Uall) (hZ : Nat.card Z = 2)
    {u a b c : X} (hu : u ∈ Uall) (huX : u ∉ UX) (ha : a ∈ Uall) (hb : b ∈ Uall) (hc : c ∈ Uall)
    (hau : u⁻¹ * a ∈ UX) (hbu : u⁻¹ * b ∈ UX) (hcu : u⁻¹ * c ∈ UX)
    (hab : a⁻¹ * b ∉ Z) (hac : a⁻¹ * c ∉ Z) (hbc : b⁻¹ * c ∉ Z) :
    Nat.card ↥(Z ⊔ Subgroup.closure ({a, b, c} : Set X)) = 16 := by
  have hZUall : Z ≤ Uall := hZU.trans hXU
  have hnotZ : ∀ {x : X}, u⁻¹ * x ∈ UX → x ∉ Z := by
    intro x hux hxZ
    apply huX
    have h1 : u⁻¹ ∈ UX := by
      have := UX.mul_mem hux (UX.inv_mem (hZU hxZ))
      simpa using this
    simpa using UX.inv_mem h1
  have ha0 : a ∉ Z := hnotZ hau
  have hb0 : b ∉ Z := hnotZ hbu
  have hc0 : c ∉ Z := hnotZ hcu
  have habX : a * b ∈ UX := by
    have hu2 : u * u = 1 := by simpa [pow_two] using hsq u hu
    have hcm : (u⁻¹ * a) * u = u * (u⁻¹ * a) :=
      hcomm _ (Uall.mul_mem (Uall.inv_mem hu) ha) u hu
    have e : a * b = (u⁻¹ * a) * (u⁻¹ * b) := by
      calc a * b = (u * (u⁻¹ * a)) * (u * (u⁻¹ * b)) := by group
        _ = u * ((u⁻¹ * a) * u) * (u⁻¹ * b) := by group
        _ = u * (u * (u⁻¹ * a)) * (u⁻¹ * b) := by rw [hcm]
        _ = (u * u) * ((u⁻¹ * a) * (u⁻¹ * b)) := by group
        _ = (u⁻¹ * a) * (u⁻¹ * b) := by rw [hu2, one_mul]
    rw [e]
    exact UX.mul_mem hau hbu
  set A₁ : Subgroup X := Z ⊔ Subgroup.zpowers a with hA₁
  set A₂ : Subgroup X := A₁ ⊔ Subgroup.zpowers b with hA₂
  set A₃ : Subgroup X := A₂ ⊔ Subgroup.zpowers c with hA₃
  have hA₁U : A₁ ≤ Uall := sup_le hZUall (Subgroup.zpowers_le.mpr ha)
  have hA₂U : A₂ ≤ Uall := sup_le hA₁U (Subgroup.zpowers_le.mpr hb)
  have hcomA : ∀ (A : Subgroup X), A ≤ Uall → ∀ {x : X}, x ∈ Uall → ∀ y ∈ A, y * x = x * y :=
    fun A hA x hx y hy => hcomm y (hA hy) x hx
  have c1 : Nat.card A₁ = 4 := by
    rw [hA₁, card_sup_zpowers_eq (hsq a ha) (hcomA Z hZUall ha) ha0, hZ]
  have hbA₁ : b ∉ A₁ := by
    rw [hA₁, mem_sup_zpowers_iff (hsq a ha) (hcomA Z hZUall ha)]
    rintro (h | h)
    · exact hb0 h
    · apply hab
      have := hcomm b hb a⁻¹ (Uall.inv_mem ha)
      rw [this] at h
      exact h
  have c2 : Nat.card A₂ = 8 := by
    rw [hA₂, card_sup_zpowers_eq (hsq b hb) (hcomA A₁ hA₁U hb) hbA₁, c1]
  have hcA₂ : c ∉ A₂ := by
    rw [hA₂, mem_sup_zpowers_iff (hsq b hb) (hcomA A₁ hA₁U hb)]
    rintro (h | h)
    · rw [hA₁, mem_sup_zpowers_iff (hsq a ha) (hcomA Z hZUall ha)] at h
      rcases h with h | h
      · exact hc0 h
      · apply hac
        have := hcomm c hc a⁻¹ (Uall.inv_mem ha)
        rw [this] at h
        exact h
    · rw [hA₁, mem_sup_zpowers_iff (hsq a ha) (hcomA Z hZUall ha)] at h
      rcases h with h | h
      · apply hbc
        have := hcomm c hc b⁻¹ (Uall.inv_mem hb)
        rw [this] at h
        exact h
      ·
        apply huX
        have hcX : c ∈ UX := by
          have e : c = (c * b⁻¹ * a⁻¹) * (a * b) := by
            have hcm : a * b = b * a := hcomm a ha b hb
            calc c = c * b⁻¹ * a⁻¹ * (a * b) := by
                  have : b⁻¹ * a⁻¹ * (a * b) = 1 := by group
                  calc c = c * (b⁻¹ * a⁻¹ * (a * b)) := by rw [this, mul_one]
                    _ = c * b⁻¹ * a⁻¹ * (a * b) := by group
              _ = (c * b⁻¹ * a⁻¹) * (a * b) := rfl
          rw [e]
          exact UX.mul_mem (hZU h) habX
        have h1 : u⁻¹ ∈ UX := by
          have := UX.mul_mem hcu (UX.inv_mem hcX)
          simpa using this
        simpa using UX.inv_mem h1
  have c3 : Nat.card A₃ = 16 := by
    rw [hA₃, card_sup_zpowers_eq (hsq c hc) (hcomA A₂ hA₂U hc) hcA₂, c2]
  have hmemR : ∀ x ∈ ({a, b, c} : Set X), x ∈ Z ⊔ Subgroup.closure ({a, b, c} : Set X) :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.subset_closure hx)
  have hA₃eq : A₃ = Z ⊔ Subgroup.closure ({a, b, c} : Set X) := by
    refine le_antisymm ?_ ?_
    · refine sup_le (sup_le (sup_le le_sup_left (Subgroup.zpowers_le.mpr (hmemR a (by simp))))
        (Subgroup.zpowers_le.mpr (hmemR b (by simp)))) (Subgroup.zpowers_le.mpr (hmemR c (by simp)))
    · refine sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers _)))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [← hA₃eq]
  exact c3

end Counting

end CFSG.Quasithin
