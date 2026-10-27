module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParLie
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmall
import CFSG.RankThree.PartTwo.Sec19.KF1923ParLn
import CFSG.RankThree.PartTwo.Sec19.KF1923Out
import CFSG.RankThree.PartTwo.Sec19.KF1923Rank
import CFSG.RankThree.PartTwo.Sec19.KF1923Small
import CFSG.RankThree.PartTwo.Sec19.KF1923L3Par
import CFSG.RankThree.PartTwo.Sec19.KF1923L3Aut

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open CFSG.RankThree.PartTwo.Sec19 (IsList194 IsSmall194 IsTripleA6)


theorem kfPar_of_sp6_o8
    (hSp6 : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSp 3 (GaloisField 2 1)) →
      NoSquareInvertingInParabolic X)
    (hO8 : ∀ (X : Type) [Group X] [Finite X], (∃ b c : GaloisField 2 1,
      (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) →
      NoSquareInvertingInParabolic X) :
    KFPar := by
  intro X _ _ hX
  have hsm := fun hs => kfPar_small (X := X) hX hs
  refine ⟨fun hnc => ?_, fun hnc => ?_⟩
  · rcases hnc with ⟨k, hk, hSL | hL⟩ | hL44 | hA6 | h3
    · exact (kfPar_lie_q4 (Or.inl ⟨2 * k, by omega, Or.inl hSL⟩)).1
    · exact (kfPar_lie_q4 (Or.inl ⟨2 * k, by omega, Or.inr (Or.inl hL)⟩)).1
    · exact (kfPar_lie_q4 (Or.inr (Or.inl hL44))).1
    · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Or.inl hA6)))))))))).1 (Or.inr (Or.inr (Or.inl hA6)))
    · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h3)))))))))).1 (Or.inr (Or.inr (Or.inr h3)))
  · rcases hX.2 with hl | hs | h3
    · rcases hl with ⟨n, hn, hSL | hL | hSp | hG2⟩ | hU42 | hU48 | hL42 | hL44 | hL52 | hL62 |
        hL72 | hSp62 | hO | hA10
      · rcases Nat.lt_or_ge n 2 with h1 | h2
        · obtain rfl : n = 1 := by omega
          exact (hsm (Or.inl hSL)).2 hnc
        · exact (kfPar_lie_q4 (Or.inl ⟨n, h2, Or.inl hSL⟩)).2
      · rcases Nat.lt_or_ge n 2 with h1 | h2
        · obtain rfl : n = 1 := by omega
          exact (hsm (Or.inr (Or.inl hL))).2 hnc
        · exact (kfPar_lie_q4 (Or.inl ⟨n, h2, Or.inr (Or.inl hL)⟩)).2
      · rcases Nat.lt_or_ge n 2 with h1 | h2
        · obtain rfl : n = 1 := by omega
          exact (hsm (Or.inr (Or.inr (Or.inl hSp)))).2 hnc
        · exact (kfPar_lie_q4 (Or.inl ⟨n, h2, Or.inr (Or.inr (Or.inl hSp))⟩)).2
      · rcases Nat.lt_or_ge n 2 with h1 | h2
        · obtain rfl : n = 1 := by omega
          exact (hsm (Or.inr (Or.inr (Or.inr (Or.inl hG2))))).2 hnc
        · exact (kfPar_lie_q4 (Or.inl ⟨n, h2, Or.inr (Or.inr (Or.inr hG2))⟩)).2
      · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU42)))))).2 hnc
      · exact (kfPar_lie_q4 (Or.inr (Or.inr hU48))).2
      · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL42))))))).2 hnc
      · exact (kfPar_lie_q4 (Or.inr (Or.inl hL44))).2
      · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL52)))))))).2 hnc
      · exact kfPar_L6_L7 (Or.inl hL62)
      · exact kfPar_L6_L7 (Or.inr hL72)
      · exact hSp6 X hSp62
      · exact hO8 X hO
      · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          hA10)))))))))).2 hnc
    · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        hs))))))))).2 hnc
    · exact (hsm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h3)))))))))).2 hnc

theorem kFacts1923_of_sp6_o8 (h194 : Sec19.Item194UsedWide3) (h316 : Sec19.Item316)
    (hSp6 : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSp 3 (GaloisField 2 1)) →
      NoSquareInvertingInParabolic X)
    (hO8 : ∀ (X : Type) [Group X] [Finite X], (∃ b c : GaloisField 2 1,
      (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) →
      NoSquareInvertingInParabolic X) :
    KFacts1923 :=
  ⟨h194, h316, kf1_holds, kf2_holds, kfBigPrime_holds, kf3a_holds, kf3b_holds, kf4_holds,
    kf5_holds, kf6_holds, kfPar_of_sp6_o8 hSp6 hO8, kfl3Par_holds, kfl3Two_holds, kfl3Aut3_holds⟩

end CFSG.RankThree.PartTwo.Late
