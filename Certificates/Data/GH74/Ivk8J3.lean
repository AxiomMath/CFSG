module

public import Certificates.Data.GH74.Ivk8Two
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import Certificates.Data.GH74.Ivk8Two
public meta import CFSG.Sporadic.SmallOddCore.J3DataInputs

public section

namespace Certificates.Ivk8Two.J3

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def gensT : List Table :=
  [j3CentTbl 1, j3CentTbl 2, j3CentTbl 3, j3CentTbl 4, j3CentTbl 5, j3CentTbl 6, j3CentTbl 7,
    j3CentTbl 8]

@[expose] def j3TwoOK : Bool :=
  twoOKT 6156 gensT [1] [2] [1, 6, 8] [6, 3, 8] [4] [-8, -8] && centralOKT 6156 gensT [1] &&
    tblEq 6156 (j3CentTbl 1) (j3CentTbl 9)

end Certificates.Ivk8Two.J3
