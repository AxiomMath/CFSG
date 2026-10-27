module

public import CFSG.Permutation.FiveTransitive.Degree24FiveIncidence
public import CFSG.Permutation.FiveTransitive.Degree24Order280
public import CFSG.Permutation.FiveTransitive.Degree24Order4
public import CFSG.Permutation.FiveTransitive.Degree24SevenTransferContradiction
public import CFSG.Permutation.FiveTransitive.Degree24SevenRSixContradiction
public import CFSG.Permutation.FiveTransitive.Degree24SevenNormalizerAction
public import CFSG.Permutation.FiveTransitive.Degree24Order8640
public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeSmallNormalizer
public import CFSG.Permutation.FiveTransitive.Degree24Order8100
public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoGoursat
public import CFSG.Permutation.FiveTransitive.Degree24FiveGoursat
public import CFSG.Permutation.FiveTransitive.Degree24ElevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24Order1152
public import CFSG.Permutation.FiveTransitive.Degree24Order4096
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerCases

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_reduced_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h = 48 ∨
    h = 96 ∨
    False := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h = 48 ∨
    h = 96 ∨
    False
  have hcases :
      h = 25 ∨ h = 15 ∨ h = 27 ∨ h = 567 ∨
      h = 50 ∨ h = 1050 ∨ h = 4 ∨ h = 140 ∨
      h = 324 ∨ h = 8100 ∨ h = 280 ∨ h = 600 ∨
      h = 360 ∨ h = 13608 ∨ h = 48 ∨ h = 1200 ∨
      h = 97200 ∨ h = 96 ∨ h = 3360 ∨ h = 2016 ∨
      h = 194400 ∨ h = 4082400 ∨ h = 14400 ∨
      h = 8640 ∨ h = 1152 ∨ h = 1088640 ∨
      h = 2332800 ∨ h = 1280 ∨ h = 2304 ∨
      h = 48384 ∨ h = 4665600 ∨ h = 89600 ∨
      h = 13063680 ∨ h = 27648 ∨ h = 691200 ∨
      h = 26127360 ∨ h = 51200 ∨ h = 30720 ∨
      h = 1161216 ∨ h = 4096 ∨ h = 102400 ∨
      h = 8294400 := by
    simpa only [H, h] using
      five_point_stabilizer_card_cases
        X P hcard h5 hnotAlt s hs
  have hnotTwentyFive : h ≠ 25 := by
    simpa only [H, h] using
      (five_point_stabilizer_card_ne_twenty_five_and_ne_fifty
        X P hcard h5 hnotAlt s hs).1
  have hnotFifty : h ≠ 50 := by
    simpa only [H, h] using
      (five_point_stabilizer_card_ne_twenty_five_and_ne_fifty
        X P hcard h5 hnotAlt s hs).2
  have hnotFifteen : h ≠ 15 := by
    simpa only [H, h] using
      (five_point_stabilizer_card_ne_fifteen_and_ne_one_hundred_forty
        X P hcard h5 hnotAlt s hs).1
  have hnotOneHundredForty : h ≠ 140 := by
    simpa only [H, h] using
      (five_point_stabilizer_card_ne_fifteen_and_ne_one_hundred_forty
        X P hcard h5 hnotAlt s hs).2
  have hnotTwoHundredEighty : h ≠ 280 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_two_hundred_eighty
        X P hcard h5 hnotAlt s hs
  have hnotFiveHundredSixtySeven : h ≠ 567 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_five_hundred_sixty_seven
        X P hcard h5 hnotAlt s hs
  have hnotTwentySeven : h ≠ 27 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_twenty_seven
        X P hcard h5 hnotAlt s hs
  have hnotFour : h ≠ 4 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_four
        X P hcard h5 hnotAlt s hs
  have hnotOneThousandFifty : h ≠ 1050 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_one_thousand_fifty
        X P hcard h5 hnotAlt s hs
  have hnotLarge :
      h ≠ 89600 ∧ h ≠ 51200 ∧ h ≠ 102400 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_eighty_nine_thousand_six_hundred_and_ne_fifty_one_thousand_two_hundred_and_ne_one_hundred_two_thousand_four_hundred
        X P hcard h5 hnotAlt s hs
  have hnotTransferCases :
      h ≠ 2016 ∧ h ≠ 1088640 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_two_thousand_sixteen_and_ne_one_million_eighty_eight_thousand_six_hundred_forty
        X P hcard h5 hnotAlt s hs
  have hnotRSixCases :
      ¬(h = 13608 ∨ h = 13063680) := by
    intro hbad
    exact
      stabilizer_card_ne_rSix_cases
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotSmallSevenNormalizerCases :
      ¬(h = 3360 ∨ h = 4082400 ∨ h = 48384 ∨
        h = 26127360 ∨ h = 1161216) := by
    intro hbad
    exact
      stabilizer_card_ne_small_seven_normalizer_cases
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotEightThousandSixHundredForty :
      h ≠ 8640 := by
    intro hbad
    exact
      five_point_stabilizer_card_ne_eight_thousand_six_hundred_forty
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotSixHundredAndTwelveHundred :
      h ≠ 600 ∧ h ≠ 1200 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_six_hundred_and_ne_twelve_hundred
        X P hcard h5 hnotAlt s hs
  have hnotEightThousandOneHundred :
      h ≠ 8100 := by
    intro hbad
    exact
      five_point_stabilizer_card_ne_eight_thousand_one_hundred
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotRemainingFiveSquared :
      ¬(h = 97200 ∨ h = 194400 ∨ h = 14400 ∨
        h = 2332800 ∨ h = 4665600 ∨ h = 691200 ∨
        h = 8294400) := by
    intro hbad
    exact
      five_point_stabilizer_card_ne_remaining_five_squared_cases
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotRemainingFive :
      ¬(h = 360 ∨ h = 1280 ∨ h = 30720) := by
    intro hbad
    exact
      five_point_stabilizer_card_ne_remaining_five_cases
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotElevenResidueFive :
      ¬(h = 324 ∨ h = 2304 ∨ h = 27648) := by
    intro hbad
    exact
      five_point_stabilizer_card_ne_eleven_residue_five_cases
        X P hcard h5 hnotAlt s hs (by
          simpa only [H, h] using hbad)
  have hnotOneThousandOneHundredFiftyTwo :
      h ≠ 1152 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_one_thousand_one_hundred_fifty_two
        X P hcard h5 hnotAlt s hs
  have hnotFourThousandNinetySix :
      h ≠ 4096 := by
    simpa only [H, h] using
      five_point_stabilizer_card_ne_four_thousand_ninety_six
        X P hcard h5 hnotAlt s hs
  omega

end FiveTransitive.Degree24

end CFSG
