module

public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofRoute
public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTwoOut
public import CFSG.RankThree.PartTwo.Sec16.Item166Res7ProofOne
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16

@[expose] def Step168TwoOutNot2nOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L → omegaA A = {Subgroup.zpowers c} → Two168Out A Y₀

theorem step168TwoOutNot2n_of_omega (hst : StellmacherKP)
    (h146 : Item146S14) (h167 : Item167R) (hQ0 : Claim17Q0) (h : Step168TwoOutNot2nOmega) :
    Step168TwoOutNot2n := by
  intro G _ _ A c L Y₀ hs hL
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  · exact h G A c L Y₀ hs hL hΩ
  · exact Proof168Res2.two168Out_of_pCoreOf_mem hs hst (h146 G A c L hs.toSec14Std)
      (h167 G A c L hs.toSec15R)
      (Proof168Res2.pCoreOf_M_mem_scriptQ hs (h146 G A c L hs.toSec14Std) (hQ0 G A c L Y₀ hs)
        fun h' => absurd h' hΩ)

theorem item168S17_of_not2n (hst : StellmacherKP)
    (h146 : Item146S14) (h167 : Item167R) (h166 : Item166S17) (hbot : Item145BotS17)
    (h165 : Item165S17) (hOut : Step168TwoOutNot2n) : Item168S17 :=
  item168S17_of hst h146 h167 (step168One_of_char2 hst h146 h167)
    (step168Two_of_not2n hst h146 h166 hbot h167 h165 hOut)

end CFSG.RankThree.PartTwo.Sec17
