
module

public import CFSG.Sporadic.SmallOddCore.J2CheckBase
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.SmallOddCore.J2CheckBase
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def j2C1Gens : List Table :=
  [j2CentTbl 18, j2CentTbl 19, j2CentTbl 20, j2CentTbl 21, j2CentTbl 22]

@[expose] def j2C2Gens : List Table := [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35]

@[expose] def j2DGens : List Table :=
  [wordTbl 315 j2C1Gens [3, 2], wordTbl 315 j2C1Gens [2, 4, 2, 4]]

@[expose] def j2DReps : List Table :=
  [wordTbl 315 j2DGens [1], wordTbl 315 j2DGens [2], wordTbl 315 j2DGens [1, 2],
    wordTbl 315 j2DGens [1, 2, 2]]

@[expose] def j2QGens : List Table :=
  [wordTbl 315 j2C2Gens [3, 3, 3, 2, 1, 2, 1], wordTbl 315 j2C2Gens [3, 3, 2, 3, 2, 1],
    wordTbl 315 j2C2Gens [2, 3, 1, 3, 3, 1], wordTbl 315 j2C2Gens [3, 3, 3],
    wordTbl 315 j2C2Gens [4, 4, 4]]

@[expose] def j2DOK : Bool :=
  let D := mulClosureH 315 j2DGens.toArray 100
  let Dg := j2DGens.toArray
  let DgInv := Dg.map (invT 315)
  enumOK 315 100 60 j2DGens && enumOK 315 300 240 j2C1Gens &&
    j2C1Gens.all (fun c => permOK 315 c) && j2DGens.all (fun c => permOK 315 c) &&
    j2DReps.all (fun c => permOK 315 c) &&
    normOK 315 100 j2DGens j2C1Gens &&
    D.1.all (fun x => tblEq 315 x (idT 315) ||
      j2DReps.any fun r => memT 315 (conjClosureH 315 Dg DgInv r 100).1 x) &&
    j2DReps.all (fun r =>
      let O := conjClosureH 315 Dg DgInv r 100
      conjTreeOK 315 Dg DgInv r O.1 O.2.1 O.2.2 &&
        (let N := mulClosureH 315 O.1 100
        mulTreeOK 315 O.1 N.1 N.2.1 N.2.2 && hkeysDistinct 315 N.1.toList && N.1.size == 60)) &&
    centCount 315 300 j2C1Gens j2DGens == 4

@[expose] def j2QOK : Bool :=
  enumOK 315 100 32 j2QGens && enumOK 315 3000 1920 j2C2Gens &&
    j2C2Gens.all (fun c => permOK 315 c) && j2QGens.all (fun c => permOK 315 c) &&
    normOK 315 100 j2QGens j2C2Gens && centCount 315 3000 j2C2Gens j2QGens == 2

end CFSG.Sporadic.SmallOddCore
