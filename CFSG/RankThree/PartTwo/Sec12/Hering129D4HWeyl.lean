module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofModelA

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

@[expose] def rhoL : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank := TwistTag.D4.perm

@[expose] def deltaW (ω : List (Fin TwistTag.D4.tag.rank)) : List (Fin TwistTag.D4.tag.rank) :=
  [2, 0] ++ ω.map rhoL ++ [0, 2]

@[expose] def wT : List (Fin TwistTag.D4.tag.rank) := [1, 2]

@[expose] def wS : List (Fin TwistTag.D4.tag.rank) := [1, 3, 2, 0, 1, 2]

@[expose] def gT2 : Exp3 := ![0, 1, 1, 2]

theorem wordProd_eq_of_wordVec {ω ω' : List (Fin TwistTag.D4.tag.rank)}
    (h : ∀ i, wordVec ω (Pi.single i 1) = wordVec ω' (Pi.single i 1)) :
    (coxeterSystem TwistTag.D4.tag).wordProd ω = (coxeterSystem TwistTag.D4.tag).wordProd ω' :=
  ext_single fun i => by rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.wordProd_smul, CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.wordProd_smul]; exact h i

theorem wordProd_deltaW_pow_four_wT :
    (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[4] wT) =
      (coxeterSystem TwistTag.D4.tag).wordProd wT :=
  wordProd_eq_of_wordVec (by decide +kernel)

theorem wordProd_deltaW_pow_four_wS :
    (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[4] wS) =
      (coxeterSystem TwistTag.D4.tag).wordProd wS :=
  wordProd_eq_of_wordVec (by decide +kernel)

theorem wordProd_deltaW_pow_ten_wT :
    (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[10] wT) =
      (coxeterSystem TwistTag.D4.tag).wordProd wT :=
  wordProd_eq_of_wordVec (by decide +kernel)

theorem wordProd_deltaW_pow_ten_wS :
    (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[10] wS) =
      (coxeterSystem TwistTag.D4.tag).wordProd wS :=
  wordProd_eq_of_wordVec (by decide +kernel)

theorem wordProd_wT_cube :
    (coxeterSystem TwistTag.D4.tag).wordProd (wT ++ wT ++ wT) = 1 := by
  rw [wordProd_eq_of_wordVec (ω' := []) (by decide +kernel)]
  exact CoxeterSystem.wordProd_nil _

theorem wordExp_wT_gT : wordExp wT gT = gT := by decide

theorem wordExp_wT_gT2 : wordExp wT gT2 = gT2 + gT := by decide

theorem wordExp_wS_gT : wordExp wS gT = -gT2 := by decide

theorem wordExp_wS_gT2 : wordExp wS gT2 = gT := by decide

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
