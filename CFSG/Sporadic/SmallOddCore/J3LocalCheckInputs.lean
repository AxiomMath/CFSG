module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def j3C1Gens : List Table :=
  [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14]

@[expose] def j3QGens : List Table :=
  [wordTbl 6156 j3C1Gens [1], wordTbl 6156 j3C1Gens [3], wordTbl 6156 j3C1Gens [5, 5],
    wordTbl 6156 j3C1Gens [4, 4, 4], wordTbl 6156 j3C1Gens [5, 3, 5]]

@[expose] def j3QOK : Bool :=
  enumOK 6156 100 32 j3QGens && enumOK 6156 3000 1920 j3C1Gens &&
    j3C1Gens.all (fun c => permOK 6156 c) && j3QGens.all (fun c => permOK 6156 c) &&
    normOK 6156 100 j3QGens j3C1Gens && centCount 6156 3000 j3C1Gens j3QGens == 2

end CFSG.Sporadic.SmallOddCore
