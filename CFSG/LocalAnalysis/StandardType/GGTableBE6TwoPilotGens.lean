module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMat
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.RelativeWeylTwist
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint TableBExc.E6Three E6TwoMat

namespace E6TwoPilot

@[expose] def uWord : Fin 4 → List ℕ :=
  ![[7, 14], [8, 16], [10, 20], [49, 56]]

@[expose] def sWord : List ℕ :=
  [47, 29, 27, 26, 30, 28, 25, 9]

@[expose] def wpow : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | n + 1, w => w ++ wpow n w

@[expose] def eWord (v : Fin 4 → ZMod 3) : List ℕ :=
  wpow (v 0).val (uWord 0) ++ wpow (v 1).val (uWord 1) ++ wpow (v 2).val (uWord 2) ++
    wpow (v 3).val (uWord 3)

@[expose] def msCol : Fin 4 → Fin 4 → ZMod 3 :=
  ![![2, 1, 1, 2], ![1, 2, 1, 2], ![1, 1, 2, 2], ![1, 1, 1, 1]]

@[expose] def tPerm : Fin 4 → Fin 4 :=
  ![1, 2, 0, 3]

theorem rootOf_uWord : ∀ i : Fin 4,
    uWord i = [(uWord i).getD 0 0, (uWord i).getD 1 0] ∧ rootOf ((uWord i).getD 0 0) = bE6 i ∧
      rootOf ((uWord i).getD 1 0) = -bE6 i := by
  decide +kernel

theorem wordsAgree_s_cube : wordsAgree (sWord ++ sWord ++ sWord) [] = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem wordsAgree_s_u0 : wordsAgree (sWord ++ uWord 0) (eWord (msCol 0) ++ sWord) = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem wordsAgree_s_u1 : wordsAgree (sWord ++ uWord 1) (eWord (msCol 1) ++ sWord) = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem wordsAgree_s_u2 : wordsAgree (sWord ++ uWord 2) (eWord (msCol 2) ++ sWord) = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

theorem wordsAgree_s_u3 : wordsAgree (sWord ++ uWord 3) (eWord (msCol 3) ++ sWord) = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

@[expose] def sWordT : List ℕ :=
  [47, 27, 26, 29, 25, 30, 28, 9]

theorem wordsAgree_sT : wordsAgree sWordT sWord = true :=
  E6TwoMatK.wordsAgree_of_K (by decide +kernel)

end E6TwoPilot

end CFSG.StandardType
