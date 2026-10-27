module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D]

theorem zpow_cases_order_four {c κ : D} (h4 : orderOf c = 4) (hcc : c * c = κ)
    (hκ : κ * κ = 1) (m : ℤ) : c ^ m = 1 ∨ c ^ m = κ ∨ c ^ m * c ^ m = κ := by
  have h := zpow_mod_orderOf c m
  rw [h4] at h
  have hm : m % ((4 : ℕ) : ℤ) = 0 ∨ m % ((4 : ℕ) : ℤ) = 1 ∨ m % ((4 : ℕ) : ℤ) = 2 ∨
      m % ((4 : ℕ) : ℤ) = 3 := by omega
  rw [← h]
  have hc4 : c * c * (c * c) = 1 := by rw [hcc, hκ]
  rcases hm with hm | hm | hm | hm <;> rw [hm]
  · left; simp
  · right; right; simpa using hcc
  · right; left; rw [zpow_two, hcc]
  · right; right
    have e : c ^ (3 : ℤ) * c ^ (3 : ℤ) = (c * c) * (c * c * (c * c)) := by
      simp only [zpow_ofNat, pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hc4, mul_one, hcc]

theorem orderOf_eq_four_of_sq {w κ : D} (hw : w * w = κ) (hκ : κ * κ = 1) (hκ1 : κ ≠ 1) :
    orderOf w = 4 := by
  have h2 : ¬ w ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hw]; exact hκ1
  have h4 : w ^ 2 ^ (1 + 1) = 1 := by
    have e : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [e, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hw, hκ]
  have := orderOf_eq_prime_pow h2 h4
  rw [this]; norm_num

theorem nonempty_mulEquiv_of_commuting_order_four [Finite D] {c c' κ κ' : D}
    (hc : c * c = κ) (hc' : c' * c' = κ') (hκ : κ * κ = 1) (hκ' : κ' * κ' = 1)
    (hκ1 : κ ≠ 1) (hκ'1 : κ' ≠ 1) (hne : κ ≠ κ') (hcomm : c * c' = c' * c) :
    Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers c') = 16 ∧
    Nonempty (↥(Subgroup.zpowers c ⊔ Subgroup.zpowers c') ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have hoc := orderOf_eq_four_of_sq hc hκ hκ1
  have hoc' := orderOf_eq_four_of_sq hc' hκ' hκ'1
  have hdisj : Subgroup.zpowers c ⊓ Subgroup.zpowers c' = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw2
    have h1 := zpow_cases_order_four hoc hc hκ m
    have h2 := zpow_cases_order_four hoc' hc' hκ' n
    rw [hn] at h2
    rcases h1 with h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exfalso
      rcases h2 with h2 | h2 | h2
      · exact hκ1 (h1.symm.trans h2)
      · exact hne (h1.symm.trans h2)
      · rw [h1, hκ] at h2
        exact hκ'1 h2.symm
    · exfalso
      rcases h2 with h2 | h2 | h2
      · rw [h2, one_mul] at h1
        exact hκ1 h1.symm
      · rw [h2, hκ'] at h1
        exact hκ1 h1.symm
      · exact hne (h1.symm.trans h2)
  have hcommZ : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ Subgroup.zpowers c', a * b = b * a := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ((show Commute c c' from hcomm).zpow_zpow m n).eq
  obtain ⟨e⟩ := GoldAmN.nonempty_mulEquiv_prod_of_sup_eq
    (Subgroup.zpowers c ⊔ Subgroup.zpowers c') (Subgroup.zpowers c) (Subgroup.zpowers c')
    le_sup_left le_sup_right rfl hcommZ hdisj
  have hcard1 : Nat.card ↥(Subgroup.zpowers c) = 4 := by rw [Nat.card_zpowers, hoc]
  have hcard2 : Nat.card ↥(Subgroup.zpowers c') = 4 := by rw [Nat.card_zpowers, hoc']
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcard1, hcard2]
  · let e₁ : ↥(Subgroup.zpowers c) ≃* Multiplicative (ZMod 4) :=
      mulEquivOfCyclicCardEq (by rw [hcard1, card_multiplicative_zmod_four])
    let e₂ : ↥(Subgroup.zpowers c') ≃* Multiplicative (ZMod 4) :=
      mulEquivOfCyclicCardEq (by rw [hcard2, card_multiplicative_zmod_four])
    exact ⟨e.trans (e₁.prodCongr e₂)⟩

theorem le_sup_zpowers_of_card_four [Finite D] {V : Subgroup D} (hV : Nat.card ↥V = 4)
    {κ κ' : D} (h1 : κ ∈ V) (h2 : κ' ∈ V) (hκ : κ * κ = 1) (hκ1 : κ ≠ 1) (hκ'1 : κ' ≠ 1)
    (hne : κ' ≠ κ) : V ≤ Subgroup.zpowers κ ⊔ Subgroup.zpowers κ' := by
  have hS : Subgroup.zpowers κ ⊔ Subgroup.zpowers κ' ≤ V :=
    sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
  have hord : orderOf κ = 2 := orderOf_eq_prime (by rwa [pow_two]) hκ1
  have hcard2 : Nat.card ↥(Subgroup.zpowers κ) = 2 := by rw [Nat.card_zpowers, hord]
  have hdvd1 : 2 ∣ Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') := by
    rw [← hcard2]; exact Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') ∣ 4 := by
    rw [← hV]; exact Subgroup.card_dvd_of_le hS
  have hne2 : Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') ≠ 2 := by
    intro h2'
    have heq : Subgroup.zpowers κ = Subgroup.zpowers κ ⊔ Subgroup.zpowers κ' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2', hcard2])
    have hmem : κ' ∈ Subgroup.zpowers κ := by
      rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers κ')
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases zpow_eq_one_or_self (show κ ^ 2 = 1 by rw [pow_two]; exact hκ) k with e | e
    · exact hκ'1 (hk.symm.trans e)
    · exact hne (hk.symm.trans e)
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') := Nat.card_pos
  have h4 : Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd2
    obtain ⟨k, hk⟩ := hdvd1
    generalize Nat.card ↥(Subgroup.zpowers κ ⊔ Subgroup.zpowers κ') = m at *
    interval_cases m <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [hV, h4])).ge

end GoldAmL3c

end F6

end CFSG.Quasithin
