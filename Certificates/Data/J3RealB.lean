module

public import Certificates.Data.K426J3
public meta import Certificates.Data.K426J3

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

set_option compiler.extract_closed false

@[expose] def j3RealBWord : List ℕ := [1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1]

@[expose] def j3WordArr (w : List ℕ) : Array ℕ :=
  w.foldr (fun l T => compA 6156 CFSG.Sporadic.Schreier.j3StrongArrs[l]! T) (idA 6156)

@[expose] def j3RealBOK (_ : Unit := ()) : Bool :=
  let g := j3WordArr j3RealBWord
  let x := j3tReps[1]!
  j3RealBWord.all (fun l => decide (l < 2)) &&
    eqA 6156 (compA 6156 g x) (compA 6156 (compA 6156 x x) g)

end CFSG.RankThree.PartTwo.KFacts.K426
