module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Main
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
open Item426Rest


theorem card_center_le_three_of_isList46 {X : Type} [Group X] [Finite X]
    (hl : CFSG.RankThree.PartTwo.Sec4.IsList46 X) (hq : CFSG.IsQuasisimple X) :
    Nat.card (Subgroup.center X) ≤ 3 := by
  by_cases hZ : Subgroup.center X = ⊥
  · rw [hZ, Subgroup.card_bot]
    norm_num
  have hcov : ∀ {S : Type} [Group S], Subgroup.center S = ⊥ →
      IsExtOf X S (Multiplicative (ZMod 3)) → IsTripleCover X S :=
    fun hZS hext => (isTripleCover_iff_isExtOf hq hZS).mpr hext
  obtain ⟨hZJ3, hZMcL, hZON⟩ := Item426.center_J3_McL_ON
  have hZA : ∀ {n : ℕ}, 4 ≤ n → Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    fun hn => alternatingGroup.center_eq_bot (by simpa using hn)
  have hZM22 : Subgroup.center Blueprint.NativeSporadic.M22 = ⊥ := by
    have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact Item426.center_eq_bot_of_isSimpleGroup (by rw [Item426.card_M22]; norm_num)
  rcases hl with ⟨p, e, _, -, -, ⟨e1⟩⟩ |
      ⟨p, e, hp, hp3, he1, he2, hSL | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨p, _, hp3, hG2' | ⟨⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩⟩ |
      (⟨n, -, ⟨e1⟩⟩ | hA6' | hA7') | (⟨s, hs, ⟨e1⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩) |
      ((⟨e, he1, -, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩) | ⟨⟨e1⟩⟩ | ⟨hZ3, hG23 | hU43'⟩)
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    have hpe : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
      have h0 : ¬ 3 ∣ p ^ e := fun h => by
        have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h3
        omega
      omega
    have hPi := CFSG.RankThree.PartTwo.KFacts.isSLThreePiAt_of_isSLThreeEpsAt (p := p) (e := e)
      he1 hSL hpe hZ
    exact (CFSG.RankThree.PartTwo.Sec13.Res5Proof.card_center_of_isSLThreePiAt hp.out he1 hPi).le
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    exact (false_of_projSU hq hZ le_rfl he1 e1).elim
  ·
    exact (false_of_chevalleyExceptional hq hZ (Or.inl rfl) hG2').elim
  ·
    exact (false_of_projSp_any hq hZ e1).elim
  ·
    exact (false_of_projSU hq hZ (by norm_num) le_rfl e1).elim
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    exact (false_of_alternating_any hq hZ e1).elim
  ·
    exact (hcov (hZA (by norm_num)) hA6').1.le
  ·
    exact (hcov (hZA (by norm_num)) hA7').1.le
  ·
    exact (false_of_sporadic46 hq hZ hs e1).elim
  ·
    simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact (hcov hZM22 hext).1.le
    · exact (hcov hZJ3 hext).1.le
    · exact (hcov hZMcL hext).1.le
    · exact (hcov hZON hext).1.le
  ·
    rcases hchev with ⟨n, hn, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨f, hG2' | hD4 | hSz | hF4 | hTits⟩
    · exact (false_of_projSL hq hZ e1).elim
    · exact (false_of_projSL hq hZ e1).elim
    · exact (false_of_projSU hq hZ le_rfl hn e1).elim
    · exact (false_of_projSp_any hq hZ e1).elim
    · exact (false_of_projSU hq hZ (by norm_num) hn e1).elim
    · exact (false_of_chevalleyExceptional hq hZ (Or.inl rfl) hG2').elim
    · exact (false_of_chevalleyExceptional hq hZ (Or.inr rfl) hD4).elim
    · exact (false_of_suzuki hq hZ hSz).elim
    · exact (false_of_reeTits hq hZ (Or.inl rfl) hF4).elim
    · exact (false_of_reeTits hq hZ (Or.inr rfl) hTits).elim
  ·
    have hpow : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
      have h0 : ¬ 3 ∣ 2 ^ n := fun h => by
        have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
        omega
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPi := CFSG.RankThree.PartTwo.KFacts.isSLThreePiAt_of_isSLThreeEpsAt (p := 2) (e := n)
      hn hSL hpow hZ
    exact (CFSG.RankThree.PartTwo.KFacts.card_center_of_isSLThreePiAt_two_pow hn hPi).le
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    exact (false_of_projSp_any hq hZ e1).elim
  ·
    exact (false_of_projSU hq hZ (by norm_num) (by norm_num) e1).elim
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    exact (false_of_projSU hq hZ le_rfl he1 e1).elim
  ·
    exact (false_of_projSL hq hZ e1).elim
  ·
    exact hZ3
  · exact hZ3

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
