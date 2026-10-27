module

public import Certificates.Data.CFSGNative.SectionRank.ON
public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure NormData where
  base : Data
  gens : List Nat
  og : Nat
  expo : Nat → Nat → Nat → Nat

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def powProdIdx : List M → (Nat → Nat) → M
  | [], _ => O.one
  | X :: xs, f => O.mul (O.pow X (f 0)) (powProdIdx xs fun k => f (k + 1))

@[expose] def normCheck [Inhabited M] (D : NormData) : Bool :=
  let R := O.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog
  let xs := D.base.outs.map fun r => R[r]!
  O.check D.base && decide (0 < D.og) &&
    (List.range D.gens.length).all fun j =>
      decide (D.gens[j]! < D.base.nregs) && O.eq (O.pow R[D.gens[j]!]! D.og) O.one &&
        (List.range xs.length).all fun i =>
          O.conjOK R[D.gens[j]!]! xs[i]! (O.powProdIdx xs fun k => D.expo j k i)

end Ops

@[expose] def onNormTable : List (List (List Nat)) :=
  [[[2, 0, 0, 0], [0, 0, 2, 0], [0, 1, 0, 0], [0, 1, 1, 2]],
    [[0, 0, 0, 1], [2, 2, 1, 2], [1, 1, 1, 0], [2, 0, 0, 0]]]

@[expose] def onNormExpo (j k i : Nat) : Nat :=
  ((onNormTable.getD j []).getD i []).getD k 0

@[expose] def onNormData : NormData where
  base := onanData
  gens := [15, 23]
  og := 4
  expo := onNormExpo

end CFSG.SectionRank.Native
