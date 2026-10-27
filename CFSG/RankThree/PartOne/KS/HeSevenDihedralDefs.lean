module

public import CFSG.RankThree.PartOne.KS.HeSevenData
public import Certificates.Data.K426Checks

public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.KFacts.K426

@[expose] def heSevenRhoWord : List (Fin 3 × Bool) :=
  [(1, true), (1, true), (2, false), (1, false), (1, false)]

@[expose] def heSevenSigmaWord : List (Fin 3 × Bool) :=
  [(1, true), (2, true), (0, true), (1, true), (1, true), (1, true)]

@[expose] def heSevenRhoArr (_ : Unit := ()) : Array ℕ := evalWA 8330 heSevenC1Gens heSevenRhoWord

@[expose] def heSevenSigmaArr (_ : Unit := ()) : Array ℕ :=
  evalWA 8330 heSevenC1Gens heSevenSigmaWord

@[expose] def heSevenDihedralOK (_ : Unit := ()) : Bool :=
  let ρ := heSevenRhoArr ()
  let σ := heSevenSigmaArr ()
  allLt 3 (fun k => validA 8330 heSevenC1Gens[k]!) &&
    eqA 8330 (powArr 8330 ρ 4) (idA 8330) && !eqA 8330 (powArr 8330 ρ 2) (idA 8330) &&
    eqA 8330 (compA 8330 σ σ) (idA 8330) &&
    eqA 8330 (compA 8330 σ (compA 8330 ρ σ)) (powArr 8330 ρ 3) &&
    allLt 4 (fun k => !eqA 8330 σ (powArr 8330 ρ k))

end CFSG.RankThree.PartOne
