module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Fixed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Strong
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Unique
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Seven
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Eight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

variable {G : Type} [Group G] [Finite G]

theorem r8103_at_of_even (D : Data G) (hSg : UC6S846.SigmaStd D) (he : evenRank G = 3)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h72 : F07.R72 D)
    (hKF7 : KStrongEmbedded72) (hK2 : KU45Syl3) (hK3 : KU45Key)
    (hK4 : KU4SylOdd) (hK5 : KU45Types) (hK6 : KU45Out) (hK7 : KU45TorusFix)
    (hK8 : KAltTen) (hK9 : KU45AltFive)
    {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hne : Even n) :
    R8103At D L P p n := by
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hne
  have hN : D.M ≤ normalizer (L : Set G) := le_normalizer_of_hyp8102 hSg hK2 hH hX
  have hpn : p ∣ 2 ^ n + 1 :=
    dvd_two_pow_add_one_of_hyp8102 hSg h76 h614 hK2 hK3 hH hX hN
  have hp := prime_of_hyp8102 hSg hH
  have hpdvd : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by exact_mod_cast hpn
  have hmod : (2 : ℤ) ^ n ≡ -1 [ZMOD p] := by
    rw [Int.modEq_iff_dvd, show -1 - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 1) by ring]
    exact dvd_neg.mpr hpdvd
  have hstr : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M :=
    fun q hq hqn =>
      stronglyEmbedded_of_dvd_two_pow_add_one hSg h76 h614 hK4 hH hX hN hpn hq hqn
  have h6 : ∀ A : Subgroup G, F08.NotationA8103 L P p n A →
      centralizer (A : Set G) ≤ D.M :=
    fun A hA =>
      centralizer_le_of_notationA8103 hSg he h72 hKF7 hK5 hK8 hK9 hH hX hN hpn hA
  have hmem : ∀ A : Subgroup G, F08.NotationA8103 L P p n A → A ∈ uniqueSet D.M :=
    fun A hA => mem_uniqueSet_of_notationA8103 hK7 hH hX hN hstr hA (h6 A hA)
  exact ⟨hne, ⟨hmod, he⟩, hstr,
    exists_notationA8103 hK5 hX hP hp.1 hp.2.1 hpn,
    exists_notationB8103 hK5 hX hP hp.1 hpn,
    hmem,
    fun B hB =>
      not_centralizer_le_of_notationB8103 hSg h614 hK2 hK5 hK7 hH hX hN hpn hstr h6 hB,
    isSylowOf_top_of_hyp8102 hSg h76 h614 hK2 hK5 hK6 hH hX hN hpn hmem⟩

theorem r8103_of_inputs (D : Data G) (hSg : UC6S846.SigmaStd D) (he : evenRank G = 3)
    (h82 : F08.R82 D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h72 : F07.R72 D)
    (hKF7 : KStrongEmbedded72) (hK1 : KU4OddRank) (hK2 : KU45Syl3) (hK3 : KU45Key)
    (hK4 : KU4SylOdd) (hK5 : KU45Types) (hK6 : KU45Out) (hK7 : KU45TorusFix)
    (hK8 : KAltTen) (hK9 : KU45AltFive) : F08.R8103 D := by
  intro L P p n hH
  exact r8103_at_of_even D hSg he h614 h76 h72 hKF7 hK2 hK3 hK4 hK5 hK6 hK7 hK8 hK9 hH
    (even_of_hyp8102 h82 hK1 hH)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
