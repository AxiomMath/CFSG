module

public import CFSG.Quasithin.Vol2.Ch10SecA312D2
public import CFSG.Quasithin.Vol2.Ch10SecA312C4

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312D

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch10.A312C

theorem l3_arith {p : ℕ} (hp : 3 < p)
    (h : p * (p ^ 2 - 1) * (p * (p ^ 2 - 1)) ∣ 2 * (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)))) :
    False := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.sub_eq_of_eq_add (show (q + 1) ^ 2 = q * (q + 2) + 1 by ring),
    Nat.sub_eq_of_eq_add (show (q + 1) ^ 3 = q * (q ^ 2 + 3 * q + 3) + 1 by ring)] at h
  have hq : 0 < q := by omega
  have hK : 0 < (q + 1) ^ 2 * q ^ 2 * (q + 2) :=
    Nat.mul_pos (Nat.mul_pos (by positivity) (pow_pos hq 2)) (by omega)
  have h1 : q + 2 ∣ 2 * (q + 1) * (q ^ 2 + 3 * q + 3) := by
    refine Nat.dvd_of_mul_dvd_mul_left hK ?_
    convert h using 1 <;> ring
  have h2 : q + 2 ∣ 2 := (Nat.dvd_add_right h1).mp ⟨2 * q ^ 2 + 4 * q + 4, by ring⟩
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem u3_arith {p : ℕ} (hp : 3 < p)
    (h : p * (p ^ 2 - 1) * (p * (p ^ 2 - 1)) ∣ 2 * (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)))) :
    False := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.sub_eq_of_eq_add (show (q + 1) ^ 2 = q * (q + 2) + 1 by ring)] at h
  have hq : 0 < q := by omega
  have hK : 0 < (q + 1) ^ 2 * q * (q + 2) ^ 2 :=
    Nat.mul_pos (Nat.mul_pos (by positivity) hq) (by positivity)
  have h1 : q ∣ 2 * (q + 1) * (q ^ 2 + q + 1) := by
    refine Nat.dvd_of_mul_dvd_mul_left hK ?_
    convert h using 1 <;> ring
  have h2 : q ∣ 2 := (Nat.dvd_add_right (dvd_mul_right q (2 * q ^ 2 + 4 * q + 4))).mp (by
    rw [show q * (2 * q ^ 2 + 4 * q + 4) + 2 = 2 * (q + 1) * (q ^ 2 + q + 1) by ring]
    exact h1)
  have := Nat.le_of_dvd (by norm_num) h2
  omega

variable {X : Type} [Group X] [Finite X] {B₁ B₂ : Subgroup X}

theorem case8s (hB₁ : ⁅B₁, B₁⁆ = B₁) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) (hB : IsAlt 5 ↥B₁) {p : ℕ} (hp : p.Prime)
    (hL : IsPSL 2 p 1 ↥(⊤ : Subgroup X)) (h8 : p % 8 = 3 ∨ p % 8 = 5) : False := by
  have h1 := dvd_card_of_alt5 hB₁ hc e hB
  have h2 : Nat.card X ∣ p * (p ^ 2 - 1) := by
    rw [← Subgroup.card_top]
    exact card_dvd_of_isPSL2 hL
  have h16 : 16 ∣ p * (p ^ 2 - 1) := ((show 16 ∣ 3600 by norm_num).trans h1).trans h2
  have hcop : Nat.Coprime (2 ^ 4) p :=
    Nat.Coprime.pow_left 4 ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have h16' : 16 ∣ p ^ 2 - 1 := hcop.dvd_of_dvd_mul_left h16
  have hsq : p ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    have hr : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
    rcases hr with h | h | h | h <;> rw [h]
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  generalize p ^ 2 = a at h16' hsq hp1
  omega

theorem case9s (hB₁ : ⁅B₁, B₁⁆ = B₁) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) {s : Bool} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hB : IsSL2 p ↥B₁)
    (hL : IsPSLEps3 s p 1 ↥(⊤ : Subgroup X) ∨ IsSLEps3 s p ↥(⊤ : Subgroup X)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have h1 := sq_dvd_of_sl2 hB₁ hc e (show 5 ≤ p by omega) hB
  cases s with
  | true =>
    have h2 : Nat.card X ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
      rw [← Subgroup.card_top]
      rcases hL with hL | hL
      · exact card_dvd_of_isPSL3 hL
      · rw [card_of_isSL3 hL]
    exact l3_arith hp3 (h1.trans (mul_dvd_mul_left 2 h2))
  | false =>
    have h2 : Nat.card X ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
      rw [← Subgroup.card_top]
      rcases hL with hL | hL
      · exact Dvd.intro _ (card_of_isPSU3 hL)
      · exact dvd_of_eq (by rw [card_of_isSU3 hL, sq_sub_one_eq, cube_add_one_eq]; ring)
    exact u3_arith hp3 (h1.trans (mul_dvd_mul_left 2 h2))

end CFSG.Quasithin.Vol2.Ch10.A312D
