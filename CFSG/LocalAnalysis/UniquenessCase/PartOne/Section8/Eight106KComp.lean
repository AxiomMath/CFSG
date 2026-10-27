module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106KCompQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106KCompAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

private theorem center_eq_bot_and_isU3 (hId : KU3Ident) (hMult : KU3Mult) {Y : Type} [Group Y]
    [Finite Y] (hYk : CFSG.Open.IsKGroup Y) (hYq : CFSG.Open.IsQuasisimple Y)
    (hZ : Odd (Nat.card (center Y))) (hY3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    {n p : ℕ} (hn : 2 ≤ n) (hne : Even n) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    {K : Subgroup Y} (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) (2 * n))
    (hSE : IsStronglyPEmbedded p (normalizer (K : Set Y))) :
    center Y = ⊥ ∧ IsU3 Y (2 * n) := by
  have hQ := R8106K.isU3_quotient_center hId hYk hYq hZ hY3 hn hne hp hpn hK hL2 hSE
  have h3K := R8106K.three_dvd_card_of_isL2_bar2 hL2
  have h3Z := R8106K.not_three_dvd_card_center (R8106K.inf_center_eq_bot_of_isL2 hL2 hZ) h3K hY3
  have hbot : center Y = ⊥ :=
    hMult Y (center Y) (2 * n) le_rfl h3Z hQ (by omega) (even_two_mul n)
      (R8106K.closure_pow_three_eq_top hYq h3Z (h3K.trans (Subgroup.card_subgroup_dvd_card K)))
  exact ⟨hbot, CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hQ⟩

theorem kComp8106_of_kFacts (hId : KU3Ident) (hMult : KU3Mult) (hF : KU3Facts) :
    KComp8106 := by
  intro Y _ _ hYk hYq hZ hY3 n p hn hne hp hpn K hK hL2 hSE W hW2 _ hWN
  obtain ⟨hbot, hU3⟩ := center_eq_bot_and_isU3 hId hMult hYk hYq hZ hY3 hn hne hp hpn hK hL2 hSE
  exact R8106K.eq_bot_of_isU3 hF hU3 (by omega) (even_two_mul n) hbot hK hL2 W hW2 hWN

variable {G : Type} [Group G] [Finite G]

theorem r8106_at_of_kFacts (hK1 : KU45Lines) (hK2 : KU45Syl3) (hK462 : UCK.K462)
    (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hId : KU3Ident) (hMult : KU3Mult)
    (hF : KU3Facts) {D : Data G} (hSg : SigmaStd D) {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (h8103 : R8103At D L P p n)
    (h8105 : R8105.R8105At D L P n) : R8106At D L P n :=
  r8106_at_of_inputs hK1 hK2 hK462 hSch (kComp8106_of_kFacts hId hMult hF) hSg hH h8103 h8105

theorem r8106_of_kFacts (hK1 : KU45Lines) (hK2 : KU45Syl3) (hK462 : UCK.K462)
    (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hId : KU3Ident) (hMult : KU3Mult)
    (hF : KU3Facts) {D : Data G} (hSg : SigmaStd D) (h8103 : F08.R8103 D)
    (h8105 : PartTwo.Inputs1719.PartOne.R8_105 D) : F08.R8106 D :=
  r8106_of_inputs hK1 hK2 hK462 hSch (kComp8106_of_kFacts hId hMult hF) hSg h8103 h8105

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
