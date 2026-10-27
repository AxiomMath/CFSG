module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace S15223P4

namespace K

variable {Q : Type*} [Group Q]

theorem card_oTwoUpper_le_three {L : Subgroup Q} (hL : Nat.card L = 6) :
    Nat.card (oTwoUpper L) ≤ 3 := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by rw [hL]; norm_num)
  have hidx : (Subgroup.zpowers g).index = 2 := by
    have h := (Subgroup.zpowers g).index_mul_card
    rw [Nat.card_zpowers, hg, hL] at h
    omega
  have hle : oTwoUpper L ≤ Subgroup.zpowers (g : Q) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxL, hxo⟩
    have hcop : Nat.Coprime 2 (orderOf (⟨x, hxL⟩ : L)) := by
      rw [Subgroup.orderOf_mk]
      exact Nat.coprime_two_left.mpr hxo
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.zpowers g :=
      (Subgroup.zpowers_le.mpr (Subgroup.sq_mem_of_index_two hidx _))
        (A4.mem_zpowers_pow_of_coprime hcop)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hfin : Finite (Subgroup.zpowers (g : Q)) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    norm_num)
  calc Nat.card (oTwoUpper L) ≤ Nat.card (Subgroup.zpowers (g : Q)) := Subgroup.card_le_of_le hle
    _ = 3 := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]

theorem le_normalizer_of_commute {A B : Subgroup Q} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set Q) := fun a ha => by
  have key : ∀ a' ∈ A, ∀ x ∈ B, a' * x * a'⁻¹ = x := fun a' ha' x hx => by
    rw [h a' ha' x hx, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [key a ha b hb]
    exact hb
  · intro hb
    have h1 := key a⁻¹ (A.inv_mem ha) _ hb
    have e : a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := by group
    rw [e] at h1
    exact h1.symm ▸ hb

theorem eq_oTwoUpper_of_card_three {P₁ P₂ N C : Subgroup Q} (e₁ : ↥P₁ ≃* Equiv.Perm (Fin 3))
    (h₂ : Nat.card P₂ = 6) (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : P₁ ⊓ P₂ = ⊥)
    (hN : ∀ x ∈ N, x ^ 3 = 1) (hNle : N ≤ P₁ ⊔ P₂) (hCN : C ≤ N) (hC : Nat.card C = 3)
    (hnorm : P₁ ≤ Subgroup.normalizer (C : Set Q)) :
    C = oTwoUpper P₁ ∨ C = oTwoUpper P₂ := by
  classical
  have h₁ : Nat.card P₁ = 6 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  obtain ⟨τ, hτ, hinv⟩ : ∃ τ ∈ P₁, ∀ a ∈ P₁, a ^ 3 = 1 → τ * a * τ⁻¹ = a⁻¹ := by
    have key : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
        Equiv.swap 0 1 * σ * (Equiv.swap 0 1)⁻¹ = σ⁻¹ := by decide
    refine ⟨((e₁.symm (Equiv.swap 0 1) : ↥P₁) : Q), (e₁.symm (Equiv.swap 0 1)).2,
      fun a ha ha3 => ?_⟩
    have h3 : e₁ ⟨a, ha⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥P₁) ^ 3 = 1 := Subtype.ext ha3
      rw [this, map_one]
    have h4 : e₁.symm (Equiv.swap 0 1) * ⟨a, ha⟩ * (e₁.symm (Equiv.swap 0 1))⁻¹ =
        (⟨a, ha⟩ : ↥P₁)⁻¹ := by
      apply e₁.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact key _ h3
    exact congrArg Subtype.val h4
  have hCbot : C ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hC; omega
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hCbot
  have hcC : (c : Q) ∈ C := c.2
  have hc3 : (c : Q) ^ 3 = 1 := hN _ (hCN hcC)
  have hc1' : (c : Q) ≠ 1 := fun h => hc1 (Subtype.ext h)
  obtain ⟨p₁, hp₁, p₂, hp₂, hcp⟩ : (c : Q) ∈ (P₁ : Set Q) * (P₂ : Set Q) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P₁ P₂ (le_normalizer_of_commute hcomm)]
    exact hNle (hCN hcC)
  have hcp : p₁ * p₂ = (c : Q) := hcp
  have hp12 : p₁ * p₂ = p₂ * p₁ := hcomm p₁ hp₁ p₂ hp₂
  have hcube : p₁ ^ 3 * p₂ ^ 3 = 1 := by
    rw [← Commute.mul_pow hp12 3, hcp]
    exact hc3
  have hp₁3 : p₁ ^ 3 = 1 := by
    have : p₁ ^ 3 ∈ P₁ ⊓ P₂ := ⟨P₁.pow_mem hp₁ 3, by
      have h := P₂.inv_mem (P₂.pow_mem hp₂ 3)
      rwa [← eq_inv_of_mul_eq_one_left hcube] at h⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hp₂3 : p₂ ^ 3 = 1 := by
    rw [hp₁3, one_mul] at hcube
    exact hcube
  have hτp₂ : τ * p₂ * τ⁻¹ = p₂ := by
    rw [hcomm τ hτ p₂ hp₂, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : τ * (c : Q) * τ⁻¹ = p₁⁻¹ * p₂ := by
    rw [← hcp]
    calc τ * (p₁ * p₂) * τ⁻¹ = (τ * p₁ * τ⁻¹) * (τ * p₂ * τ⁻¹) := by group
      _ = p₁⁻¹ * p₂ := by rw [hinv p₁ hp₁ hp₁3, hτp₂]
  have hc'C : p₁⁻¹ * p₂ ∈ C := by
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hτ) c).mp hcC
  have hsq₁ : p₁ * p₁ ∈ C := by
    have : p₁ * p₁ = (p₁ * p₂) * (p₁⁻¹ * p₂)⁻¹ := by group
    rw [this, hcp]
    exact C.mul_mem hcC (C.inv_mem hc'C)
  have hsq₂ : p₂ * p₂ ∈ C := by
    have : p₂ * p₂ = (p₁ * p₂) * (p₁⁻¹ * p₂) := by
      calc p₂ * p₂ = (p₂ * p₁) * (p₁⁻¹ * p₂) := by group
        _ = (p₁ * p₂) * (p₁⁻¹ * p₂) := by rw [hp12]
    rw [this, hcp]
    exact C.mul_mem hcC hc'C
  have hp₁C : p₁ ∈ C := by
    have h3 : p₁ * p₁ * p₁ = 1 := by rw [← pow_three']; exact hp₁3
    have : p₁ = (p₁ * p₁) * (p₁ * p₁) := by
      calc p₁ = (p₁ * p₁ * p₁) * p₁ := by rw [h3, one_mul]
        _ = (p₁ * p₁) * (p₁ * p₁) := by group
    rw [this]
    exact C.mul_mem hsq₁ hsq₁
  have hp₂C : p₂ ∈ C := by
    have h3 : p₂ * p₂ * p₂ = 1 := by rw [← pow_three']; exact hp₂3
    have : p₂ = (p₂ * p₂) * (p₂ * p₂) := by
      calc p₂ = (p₂ * p₂ * p₂) * p₂ := by rw [h3, one_mul]
        _ = (p₂ * p₂) * (p₂ * p₂) := by group
    rw [this]
    exact C.mul_mem hsq₂ hsq₂
  have hfin : ∀ {P : Subgroup Q} {p : Q}, Nat.card P = 6 → p ∈ P → p ^ 3 = 1 → p ≠ 1 → p ∈ C →
      C = oTwoUpper P := by
    intro P p hP hpP hp3 hp1 hpC
    have hFC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
    have hFP : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
    have hFO : Finite (oTwoUpper P) :=
      Finite.of_injective (Subgroup.inclusion (oTwoUpper_le P)) (Subgroup.inclusion_injective _)
    have hord : orderOf p = 3 := orderOf_eq_prime hp3 hp1
    have hzC : Subgroup.zpowers p ≤ C := Subgroup.zpowers_le.mpr hpC
    have hzO : Subgroup.zpowers p ≤ oTwoUpper P :=
      Subgroup.zpowers_le.mpr (mem_oTwoUpper_of_odd hpP (by rw [hord]; decide))
    have hzcard : Nat.card (Subgroup.zpowers p) = Nat.card C := by rw [Nat.card_zpowers, hord, hC]
    have hCz : Subgroup.zpowers p = C :=
      Subgroup.eq_of_le_of_card_ge hzC (by rw [hzcard])
    exact Subgroup.eq_of_le_of_card_ge (hCz ▸ hzO) ((card_oTwoUpper_le_three hP).trans hC.ge)
  by_cases hp1 : p₁ = 1
  · have hp2 : p₂ ≠ 1 := fun h2 => hc1' (by rw [← hcp, hp1, h2, one_mul])
    exact Or.inr (hfin h₂ hp₂ hp₂3 hp2 hp₂C)
  · exact Or.inl (hfin h₁ hp₁ hp₁3 hp1 hp₁C)

end K

end S15223P4

end CFSG.Quasithin
