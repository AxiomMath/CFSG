module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.RankThree.PartOne.S11b.Sec109LnTwoOuter
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.Quasithin.H23Out

theorem noFiveOut_alternating {n : ℕ} (hn : 5 ≤ n) : NoFiveOut (alternatingGroup (Fin n)) := by
  apply NoFiveOut.of_card_outer_le_four
  by_cases h6 : n = 6
  · subst h6
    exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
  · have h : n = 5 ∨ 7 ≤ n := by omega
    exact (Nat.le_of_dvd (by norm_num)
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup h).2).trans (by norm_num)

theorem out5Pow_alternating {n : ℕ} (hn : 5 ≤ n) : Out5Pow (alternatingGroup (Fin n)) :=
  Out5Pow.of_noFiveOut (noFiveOut_alternating hn)

theorem noFiveOut_of_isPSL_two {n : ℕ} {X : Type} [Group X] [Finite X] (h : IsPSL n 2 1 X) :
    NoFiveOut X :=
  NoFiveOut.of_card_outer_le_four
    ((CFSG.RankThree.PartOne.Sec109.lnTwoOuter X n h).2.trans (by norm_num))

theorem out5Pow_of_isPSL_two {n : ℕ} {X : Type} [Group X] [Finite X] (h : IsPSL n 2 1 X) :
    Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isPSL_two h)

theorem noFiveOut_statedSL_three_two :
    NoFiveOut ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
  have hGL : NoFiveOut CFSG.QuasithinUnique.Setup.Family.GL32 :=
    NoFiveOut.of_card_mulAut_le CFSG.QuasithinUnique.Setup.Family.center_GL32 (by
      rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32,
        CFSG.LieType.SteinbergBR.AutGL32.card_GL32]
      norm_num)
  exact NoFiveOut.of_mulEquiv
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3)) hGL

theorem out5Pow_statedSL_three_two :
    Out5Pow ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
  Out5Pow.of_noFiveOut noFiveOut_statedSL_three_two

end CFSG.Quasithin.H23Out
