module

public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore

@[expose] def j3NineWord : List ℕ := [
    1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
    1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]

@[expose] def j3NineTbl (_ : Unit := ()) : Table :=
  j3NineWord.foldl (fun T l => compT 6156 T j3PGTbls[l]!) (idT 6156)

@[expose] def j3NineOK : Bool :=
  let c := j3NineTbl ()
  permOK 6156 (j3CentTbl 21) && permOK 6156 c && commTT 6156 c (j3CentTbl 21) &&
    ordTest 6156 9 c

end CFSG.RankThree.PartTwo.Sec21.Hering214
