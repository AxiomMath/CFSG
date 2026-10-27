module

public import CFSG.RankThree.PartOne.N143.Final
public import CFSG.RankThree.PartOne.N143.JA
public import CFSG.RankThree.PartOne.N143.JKt
public import CFSG.RankThree.PartOne.N143.JKt1

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem jFacts_of_kfacts
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : JLemmaF) (hK2 : JLemmaK2) (h42 : JLemma42) (hB : JLemmaB) : JFacts :=
  ⟨jFactX0_holds hGA, hF, hK2, jLemmaA_holds hGA, jLemmaKt_holds hGA, jLemmaKt1_holds hGA, h42, hB⟩

theorem Node143CommB2.toSup (h : Node143CommB2) : Node143CommB2Sup := by
  intro G _ _ p A c L E hyp h12 h13 hnotFive hEA hallL3 hthree hess hmodel hC3 _ x z hxL hx3 hz hxz
  exact h G p A c L E hyp h12 h13 hnotFive hEA hallL3 hthree hess hmodel hC3 x z hxL hx3 hz hxz

theorem node143Comm_of_kfacts_sup_gen {Q : (X : Type) → [Group X] → Prop} 
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchreier : SchreierFor InCatalog) (hRow1 : KF123Row 1) (h107 : InSec10Seven)
    (h109 : InSec10Nine) (h122 : Node122) (hpair : KF134Pair)
    (hF : JLemmaF) (hK2 : JLemmaK2) (h42 : JLemma42) (hB : JLemmaB)
    (hB2 : Node143CommB2Sup) (h64W : KF64WWith Q) (h613 : Item613With Q) : Node143Comm :=
  node143Comm_of_jfacts hSchreier hRow1 h107 h109 h122 hpair (jFacts_of_kfacts hGA hF hK2 h42 hB)
    hB2 h64W h613

end CFSG.RankThree.PartOne.N143
