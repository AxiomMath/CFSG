module

public meta import Certificates.Data.Kernel.MaxD2.Gen

public section

namespace CFSG.KS.MaxD2.Gen

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

meta def closHints (D : Data) (P : Pre) (i : Nat) : Array Nat :=
  let n := D.n
  let idx := indexOf P.nT
  let x := P.rep[i]!
  let xi := P.repi[i]!
  let cnt := P.nT.size
  P.nT.map fun a =>
    let y := comp n (comp n x a) x
    match idx.get? y with
    | some e => 2 * e + 1
    | none =>
      match (List.range cnt).findSome? fun l =>
          (idx.get? (comp n (comp n xi P.nT[l]!) y)).map fun e => (l, e) with
      | some (l, e) => 2 * (l + 65536 * e)
      | none => 0

end CFSG.KS.MaxD2.Gen

end
