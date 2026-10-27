module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.Monster.B.Co2.Native CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

@[expose] def heN0W : List Int :=
  [1, 1, -2, -1, -2, 1, -2, -1, -1, 2, 2, -1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2,
   1, 2, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, 2,
   1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1,
   -2, 1, 2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1,
   -2, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, 2,
   1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1,
   -2, 1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2,
   -1, 2, -1, 2, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1,
   -2, 1, 2, 1, 2, 1, -2, 1, 2]

@[expose] def heN0Check (_ : Unit := ()) : Bool :=
  let N := heThreeArr heN0W
  let Ni := invCand 8330 N
  let X := heThreeBA
  let F := compA 8330 N (compA 8330 X Ni)
  lettersOK 2 heN0W && lettersOK 2 (heThreeWordsA.getD 0 []) && isInvA 8330 N Ni &&
    eqA 8330 (compA 8330 F X) (compA 8330 X F) && !(eqA 8330 F (idA 8330)) &&
    !(eqA 8330 F X) && !(eqA 8330 F (compA 8330 X X)) &&
    eqA 8330 (compA 8330 N (compA 8330 F Ni)) (compA 8330 X F)

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
