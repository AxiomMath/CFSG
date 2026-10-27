module

public import Certificates.Data.MaxD2Perm

public section

namespace Certificates.MaxD2Perm

open CFSG.PSL3Four.Native

@[expose] def transConj (D : Data) : Array Tab :=
  Array.ofFn (n := (nEnum D).tabs.size) fun k =>
    conjTab D.n (nEnum D).tabs[k.val]! (invTab D.n (nEnum D).tabs[k.val]!) (rGens D)[0]!

@[expose] def checkTrans (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let rT := (rEnum D).tabs
  let cT := transConj D
  let cIdx := indexOf cT
  invsOK D.n nT (nT.map (invTab D.n)) &&
    allBelow rT.size fun k => rT[k]! == idTab D.n || found cIdx cT rT[k]!

end Certificates.MaxD2Perm
