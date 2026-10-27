module

public import Certificates.Data.GH74J2CentCheck
public meta import Certificates.Data.GH74J2CentCheck

public section

namespace CFSG.GH74.Generic.S45.EvSpor

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def m12A1T : Table :=
  #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5, 15, 13, 21, 12, 22, 23, 18, 19, 20, 14, 16, 17]

@[expose] def m12B1T : Table :=
  #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10, 17, 20, 13, 12, 19, 15, 22, 21, 14, 16, 23, 18]

@[expose] def m12DGens : Array Table := #[m12A1T, m12B1T]

@[expose] def m12WA : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0]

@[expose] def m12WB : List Nat :=
  [0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1]

@[expose] def m12WY : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3]

@[expose] def m12WX : List Nat := [0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0]

@[expose] def m12TA : Table := evalWord 24 m12DGens m12WA

@[expose] def m12TB : Table := evalWord 24 m12DGens m12WB

@[expose] def m12TY : Table := evalWord 24 m12DGens m12WY

@[expose] def m12TX : Table := evalWord 24 m12DGens m12WX

@[expose] def m12DataOK : Bool :=
  tblEq 24 (powT 24 4 m12TA) (idT 24) && tblEq 24 (powT 24 4 m12TB) (idT 24) &&
    commTT 24 m12TA m12TB && tblEq 24 (compT 24 m12TY m12TY) (idT 24) &&
    tblEq 24 (compT 24 m12TX m12TX) (idT 24) && commTT 24 m12TY m12TX &&
    tblEq 24 (conjT 24 m12TY (invT 24 m12TY) m12TA) m12TB &&
    tblEq 24 (conjT 24 m12TY (invT 24 m12TY) m12TB) m12TA &&
    tblEq 24 (conjT 24 m12TX (invT 24 m12TX) m12TA) (invT 24 m12TA) &&
    tblEq 24 (conjT 24 m12TX (invT 24 m12TX) m12TB) (invT 24 m12TB) &&
    enumOK 24 cap [m12TA, m12TB, m12TY, m12TX] 64

end CFSG.GH74.Generic.S45.EvSpor
