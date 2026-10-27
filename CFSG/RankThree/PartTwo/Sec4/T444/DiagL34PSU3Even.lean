module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34Section
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem l34SectionPSU3Even_holds : L34SectionPSU3Even := by
  intro e he hsec
  have hf : 1 ≤ e := by
    obtain ⟨k, hk⟩ := he
    omega
  have h2 : 2 ≤ 2 ^ e := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
    rwa [pow_one] at h
  have h4 : 4 ≤ (2 ^ e) ^ 2 := by nlinarith [h2]
  have hkey := KFacts.KS14.card_projSU_three_mul_gcd 2 e hf
  haveI : Finite (projSU 3 2 e) := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    rw [h0, zero_mul] at hkey
    have hpos : 0 < (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) :=
      Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by positivity))
    exact (Nat.pos_iff_ne_zero.mp hpos) hkey.symm
  have hd := KFacts.L34.hasSection_card_dvd hsec
  rw [KFacts.L34.card_projSL] at hd
  have h5 : 5 ∣ Nat.card (projSU 3 2 e) := (by norm_num : (5 : ℕ) ∣ 20160).trans hd
  have h5' : 5 ∣ (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
    rw [← hkey]
    exact Dvd.dvd.mul_right h5 _
  have h5'' : 5 ∣ (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
    rw [mul_assoc]
    exact h5'
  exact not_five_dvd_su_three_order he h5''

end CFSG.RankThree.PartTwo.Sec4

end
