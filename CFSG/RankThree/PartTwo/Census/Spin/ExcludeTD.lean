module

public import CFSG.RankThree.PartTwo.Census.Spin.Exclude
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDTheta
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem typeTwistedD_mk_data (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid) :
    (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic = q.p ∧
      (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder = q.p ^ q.exponent ∧
      (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldExponent = q.exponent ∧
      (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.rank = r :=
  ⟨LieTypeIndex.characteristic_twistedD r q, (LieTypeIndex.fieldOrder_twistedD r q).trans
    q.card_def, LieTypeIndex.fieldExponent_twistedD r q, rfl⟩

theorem excluded433_twistedD_odd (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p ≠ 2) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) := by
  obtain ⟨hchar, -, hexp, -⟩ := typeTwistedD_mk_data r q hv
  have hodd : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic ≠ 2 :=
    hchar ▸ hp
  have hf1 := q.exponent_pos
  exact excluded433_twistedD_of_four hv
    (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic_prime hodd
    (by rw [hexp]; omega) (CarrierTD.hasWitness_theta _ hodd)

theorem excluded433_twistedD_even (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) (hf : 2 ≤ q.exponent)
    (h44 : ¬ (r = 4 ∧ q.exponent = 2)) : Excluded433 (.lie ⟨.twistedD r q, hv⟩) := by
  obtain ⟨hchar, hord, -, hrank⟩ := typeTwistedD_mk_data r q hv
  rw [hp] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.fieldOrder := by
    rw [hord]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 4 ≤ r := CarrierTD.four_le ⟨⟨.twistedD r q, hv⟩, by simp⟩
  rcases (show r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with h | h | h
  · have hf3 : 3 ≤ q.exponent := by omega
    obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hf3
    exact excluded433_twistedD_of_three hv hs (by omega) le_rfl
      (CarrierTD.hasWitness_torus_four _ hchar hq4 hs (by omega) (hord ▸ hsd) (hrank.trans h))
  · obtain ⟨s, hs, hs2, -, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
    exact excluded433_twistedD_of_four hv hs hs2 le_rfl
      (CarrierTD.hasWitness_torus_five _ hchar hq4 hs hs2 (hord ▸ hsd) (hrank.trans h))
  · obtain ⟨s, hs, hs2, hs5, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf
    exact excluded433_twistedD_of_four hv hs hs2 le_rfl
      (CarrierTD.hasWitness_torus_six _ hchar hq4 hs hs5 (hord ▸ hsd) h)

end CFSG.RankThree.PartTwo.Census.Spin
