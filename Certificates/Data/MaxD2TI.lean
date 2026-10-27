module

public import Certificates.Data.MaxD2Perm

public section

namespace Certificates.MaxD2TI

open CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

@[expose] def checkTI (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let fpT := nT.map (fpTab D.fpPts)
  let fpIdx := indexOf fpT
  let rep := repT D
  let repi := repI D
  allBelow D.repW.length fun i =>
    conjCount D.n D.fpPts fpIdx fpT nT repi[i + 1]! rep[i + 1]! % D.p != 0

end Certificates.MaxD2TI
