module

public import Certificates.Data.CFSGNative.J4.Tables
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def posTable (O : VOrb) (t : Array V2) : Table :=
  O.pts.map fun p => UInt32.ofNat (vfind O.pts O.slots O.bits (frApply t p) - 1)

@[expose] def strongTables (m : Nat) (gens : Array Table) (words : List (List Int)) :
    Array Table :=
  let invs := gens.map (invT m)
  gens ++ (words.map fun w => wordT m (fun l => if 0 < l then gens[l.toNat - 1]?.getD (idT m)
    else invs[(-l).toNat - 1]?.getD (idT m)) w).toArray

@[expose] def chainLetters (m : Nat) (strong : Array Table) : Array Table :=
  Array.ofFn (n := 2 * strong.size) fun i =>
    if i.val % 2 = 0 then strong[i.val / 2]! else invT m strong[i.val / 2]!

end CFSG.Sporadic.J4.Native
