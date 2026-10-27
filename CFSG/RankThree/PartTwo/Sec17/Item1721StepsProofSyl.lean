module

public import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofT

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16
open CFSG.Assembly.RankThreeEven (projImage)

namespace Proof1721

theorem mod_nine_of_dvd_sl3Order {q : ℕ} (hq : q % 3 = 1)
    (h : 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) : q % 9 = 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 1) ^ 3 * (3 * b * (3 * b + 2)) * (9 * b * (3 * b ^ 2 + 3 * b + 1)) =
      27 * (b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, h3, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)] at h
  have hU : ¬ 3 ∣ (3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega
  have hb : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow
    (((Nat.Prime.dvd_mul Nat.prime_three).mp h).resolve_right hU)
  omega

theorem mod_nine_of_dvd_su3Order {q : ℕ} (hq : q % 3 = 2)
    (h : 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) : q % 9 = 8 := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 2) ^ 3 * (3 * (3 * b + 1) * (b + 1)) * ((3 * b + 2) ^ 3 + 1) =
      27 * ((b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)] at h
  have hU : ¬ 3 ∣ (3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega
  have hb : 3 ∣ b + 1 := Nat.prime_three.dvd_of_dvd_pow
    (((Nat.Prime.dvd_mul Nat.prime_three).mp h).resolve_right hU)
  omega

theorem mod_nine_of_dvd_card {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (h27 : 27 ∣ Nat.card (projImage (Sec4.slPi π 3 (p ^ f) K))) :
    p ^ f % 9 = 1 ∨ p ^ f % 9 = 8 := by
  have h81 : 81 ∣ (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) *
      cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
    rw [← card_projImage_slPi_mul_three hK hq, show (81 : ℕ) = 27 * 3 by norm_num]
    exact mul_dvd_mul_right h27 3
  cases π
  · exact Or.inr (mod_nine_of_dvd_su3Order hq h81)
  · exact Or.inl (mod_nine_of_dvd_sl3Order hq h81)

end Proof1721

theorem claim1721SylL3_of (h1715 : Item1715) (h138 : Item138N) : Claim1721SylL3 := by
  intro G _ _ A c L Y₀ Y₁ S p P h hL3
  have hs := h.toSec17Std
  refine Proof1721.not_dvd_card_L_of_quot ?_
  rcases h1715 G A c L Y₀ hs with ⟨-, -, hprod, -⟩ | ⟨-, ⟨φ⟩, -, -, -⟩
  · obtain ⟨p', e, _, he, hiso⟩ := hL3
    have h9 := not_modNine_of_inner hs.toSec15R h138 KFacts.kSL3PiOrder3TypeC he hiso hprod
    obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := exists_projImage_model he hiso
    intro h27
    rw [Nat.card_congr ψ.toEquiv] at h27
    exact h9 (Proof1721.mod_nine_of_dvd_card hK hq h27)
  · rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

end CFSG.RankThree.PartTwo.Sec17
