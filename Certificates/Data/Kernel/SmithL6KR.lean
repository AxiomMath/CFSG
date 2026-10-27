module

public import Certificates.Data.Kernel.SmithL6KO
public import Certificates.Data.SmithL6Tr

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def colsF (P : List Nat) (f : Nat → Nat) : List Nat :=
  (List.range 9).map fun j => uco[P.findIdx (· == f ugens[j]!)]!

@[expose] def fixW0K (P : List Nat) (f : Nat → Nat) : Bool := P.all fun p => P.contains (f p)

@[expose] def tauP (C I k : Nat) : Nat :=
  fldW 11 I (64 * trSw (fldW 12 C k % 64) + trSw (fldW 12 C k / 64))

@[expose] def conjK (g M : List Nat) : List Nat := g.map (apK (M.map (apK g)))

@[expose] def rootK (R L : List (List Nat)) (v : Nat) : Bool := R.any (· == L.getD v [])

@[expose] def edgeK (G L : List (List Nat)) (g u v : Nat) : Bool :=
  conjK (G.getD g []) (L.getD v []) == L.getD u []

end CFSG.SmithL6.K
