module

public import Certificates.Data.MaxD2Heis

public section

namespace Certificates.MaxD2Perm

open CFSG.PSL3Four.Native

@[expose] def checkNonComm (D : Data) : Bool :=
  let nG := nGens D
  let nGI := nGensI D
  let rT := (rEnum D).tabs
  let rIdx := indexOf rT
  anyBelow nG.size fun i => anyBelow nG.size fun j =>
    !(found rIdx rT (commTab D.n nG[i]! nG[j]! nGI[i]! nGI[j]!))

end Certificates.MaxD2Perm

namespace Certificates.MaxD2Heis

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

@[expose] def checkHNonComm (D : Data) : Bool :=
  let nG := nGens D
  let nGI := nGensI D
  let rT := (hrEnum D).tabs
  let rIdx := indexOf rT
  anyBelow nG.size fun i => anyBelow nG.size fun j =>
    !(found rIdx rT (commTab D.n nG[i]! nG[j]! nGI[i]! nGI[j]!))

end Certificates.MaxD2Heis
