module

public import CFSG.Quasithin.Vol2.Ch10SecE9A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]

theorem card_eq_three_of_pCoreOf_eq_bot (hp5 : 5 ≤ p)
    (e : Q ≃* PSL(2, ZMod p)) {Y : Subgroup Q} (hY1 : Y ≠ ⊥) (hYO : oTwoUpper Y = Y)
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (hO : pCoreOf 2 Y = ⊥) : Nat.card Y = 3 := by
  rcases C10P34.card_eq_three_or_alt4 hp5 e hY1 hYO hY3 with h | hA
  · exact h
  · obtain ⟨eA⟩ := hA
    have h12 : Nat.card Y = 12 := by rw [Nat.card_congr eA.toEquiv, C10P34.card_alt4]
    have h4 := C10P34.card_pCoreOf_eq_four h12 hY3
    rw [hO, Subgroup.card_bot] at h4
    omega

theorem mem_centralizer_of_normalizes (h8 : p % 8 = 3 ∨ p % 8 = 5) (e : Q ≃* PSL(2, ZMod p))
    {S Y Z : Subgroup Q} (hS : IsSylowTwoOf S ⊤) (hY : Nat.card Y = 3)
    (hSY : S ≤ Subgroup.normalizer (Y : Set Q)) (hCZ : S ⊓ Subgroup.centralizer (Y : Set Q) ≤ Z)
    (hZS : Z ≤ S) (hZne : Z ≠ S) {a : Q} (hao : Odd (orderOf a))
    (haZ : ∀ u ∈ Z, a * u * a⁻¹ ∈ Z) : a ∈ Subgroup.centralizer (Y : Set Q) := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hK := isKleinFour_of_sylow h8 e hS
  have hS4 : Nat.card S = 4 := hK.card_four
  have hidx := C10P34.relIndex_centralizer_dvd_two hY hSY
  set C := S ⊓ Subgroup.centralizer (Y : Set Q) with hC
  have hCS : C ≤ S := inf_le_left
  have hcardC : 2 ≤ Nat.card C := by
    have hrel : Nat.card C * C.relIndex S = Nat.card S := by
      rw [← Subgroup.relIndex_bot_left C, ← Subgroup.relIndex_bot_left S,
        Subgroup.relIndex_mul_relIndex ⊥ C S bot_le hCS]
    rw [hS4] at hrel
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h <;> rw [h] at hrel <;> omega
  have hcardZ : Nat.card Z = 2 := by
    have hZdvd : Nat.card Z ∣ 4 := hS4 ▸ Subgroup.card_dvd_of_le hZS
    have hZge : 2 ≤ Nat.card Z := hcardC.trans (Subgroup.card_le_of_le hCZ)
    have hZne4 : Nat.card Z ≠ 4 := fun h4 =>
      hZne (Subgroup.eq_of_le_of_card_ge hZS (by rw [h4, hS4]))
    have h4 : Nat.card Z ≤ 4 := Nat.le_of_dvd (by norm_num) hZdvd
    interval_cases h : Nat.card Z
    · rfl
    · exact absurd hZdvd (by norm_num)
    · exact absurd rfl hZne4
  obtain ⟨z, hzC, hz1⟩ : ∃ z ∈ C, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : C = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hcardC
    omega
  have hz2 : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzC.1⟩ : ↥S))
    exact orderOf_eq_prime (by rw [sq]; exact h) hz1
  have haz : a * z * a⁻¹ = z := by
    have hzZ : z ∈ Z := hCZ hzC
    have hazZ := haZ z hzZ
    have hne : a * z * a⁻¹ ≠ 1 := fun h => hz1 (by
      have : z = a⁻¹ * (a * z * a⁻¹) * a := by group
      rw [this, h]; group)
    have hZz : Subgroup.zpowers z = Z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
        (by rw [Nat.card_zpowers, hz2, hcardZ])
    rw [← hZz] at hazZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hazZ
    rw [← zpow_mod_orderOf, hz2, Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact absurd hk.symm hne
    · rw [h1, zpow_one] at hk
      exact hk.symm
  have haz' : a * z = z * a := by
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [haz]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyz : y * z = z * y := Subgroup.mem_centralizer_iff.mp hzC.2 y hy
  have hyo : Odd (orderOf y) := by
    have h1 : orderOf (⟨y, hy⟩ : ↥Y) ∣ 3 := hY ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (by decide) h1
  exact (commute_of_mem_centralizer_involution hp2 e hz2 haz' hyz hao hyo).symm

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
