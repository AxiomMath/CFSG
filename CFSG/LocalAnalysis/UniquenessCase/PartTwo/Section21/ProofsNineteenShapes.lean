module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

variable {G : Type} [Group G] [Finite G]

private theorem pRank_three_eq_one_and_thin8_of_isL2 {K : Subgroup G} {n : ℕ}
    (h : IsL2 (Bar2 K) n) :
    CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ m : ℕ, IsU3 (Bar2 K) m) :=
  ⟨pRank_three_eq_one_of_isL2 h, Or.inl (thin8_of_isL2 h)⟩

private theorem pRank_three_eq_one_and_thin8_of_isU3 {K : Subgroup G} {m : ℕ}
    (hm : IsPowTwo m) (h : IsU3 (Bar2 K) m) :
    CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n) := by
  have hm2 : 2 ≤ m := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 h
  exact ⟨pRank_three_eq_one_of_isU3FourPow h hm hm2, Or.inr ⟨m, h⟩⟩

private theorem pRank_three_eq_one_and_thin8_of_isJ1 {K : Subgroup G}
    (h : IsJ1 (Bar2 K)) :
    CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n) := by
  have h3bar : 3 ∣ Nat.card (Bar2 K) := by
    rw [(kJ1_holds (Bar2 K) h).1]
    norm_num
  have h3 : 3 ∣ Nat.card K :=
    (dvd_card_iff_dvd_card_bar2 Nat.prime_three (by norm_num)).mpr h3bar
  exact ⟨pRank_three_eq_one_of_thin_of_dvd (thin8_of_isJ1_bar2 h) h3,
    Or.inl (thin8_of_isJ1_bar2 h)⟩

private theorem pRank_three_eq_one_and_thin8_of_isL2Odd {K : Subgroup G} {q : ℕ}
    (h : IsL2Odd (Bar2 K) q) :
    CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n) := by
  obtain ⟨hq, hq2, -⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_five_le_of_isL2Odd h
  exact ⟨pRank_three_eq_one_of_isL2Odd h,
    Or.inl (thin8_of_isL2Odd_bar2 hq hq2 h)⟩

theorem pRank_three_eq_one_and_thin8_or_isU3 {K : Subgroup G}
    (hK : (∃ n : ℕ, IsL2 (Bar2 K) n) ∨ (∃ m : ℕ, IsPowTwo m ∧ IsU3 (Bar2 K) m) ∨
      IsJ1 (Bar2 K) ∨ ∃ q : ℕ, q.Prime ∧ IsL2Odd (Bar2 K) q) :
    CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n) := by
  rcases hK with ⟨n, h⟩ | ⟨m, hm, h⟩ | h | ⟨q, -, h⟩
  · exact pRank_three_eq_one_and_thin8_of_isL2 h
  · exact pRank_three_eq_one_and_thin8_of_isU3 hm h
  · exact pRank_three_eq_one_and_thin8_of_isJ1 h
  · exact pRank_three_eq_one_and_thin8_of_isL2Odd h

theorem mem_uniqueSet_of_card_eq_three (D : Data G) (h8107 : F08.R8107 D) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K)
    (hL3 : CFSG.Open.pRank 3 L = 1 ∧ (F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n))
    (hK3 : CFSG.Open.pRank 3 K = 1 ∧ (F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n))
    {A : Subgroup G} (hAL : A ≤ L) (hA : Nat.card A = 3) : A ∈ uniqueSet D.M := by
  have h3K : 3 ∣ Nat.card K := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [hK3.1]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  let A₂ : Subgroup G := Subgroup.zpowers ((x : ↥K) : G)
  have hxG : orderOf ((x : ↥K) : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hA₂K : A₂ ≤ K := Subgroup.zpowers_le.mpr x.2
  have hA₂3 : Nat.card A₂ = 3 := by
    rw [show A₂ = Subgroup.zpowers ((x : ↥K) : G) from rfl, Nat.card_zpowers, hxG]
  exact (h8107 L hL K hK hLK hL3.1 hK3.1 hL3.2 hK3.2 A A₂ hAL hA hA₂K hA₂3).1

end CFSG.LocalAnalysis.UniquenessCase.UC22
