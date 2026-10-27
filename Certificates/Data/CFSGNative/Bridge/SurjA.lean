module

public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.HS.Cert
public import Certificates.Data.CFSGNative.McL.Certificate
public import Certificates.Data.CFSGNative.He.Certificate
public import Certificates.Data.CFSGNative.J3.Check
public import Certificates.Data.CFSGNative.Fi22.Certificate

public section

namespace CFSG.Sporadic.Bridge.TwoGen.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def letterTab (α αi β βi : Table) (l : Nat × Bool) : Table :=
  if l.1 = 0 then (if l.2 then α else αi) else if l.2 then β else βi

@[expose] def wordTab (n : Nat) (α αi β βi : Table) (v : List (Nat × Bool)) : Table :=
  v.foldr (fun l T => compT n (letterTab α αi β βi l) T) (idT n)

@[noinline, expose] def relCheck (n : Nat) (α αi β βi : Table) (rels : List (List (Nat × Bool))) :
    Bool :=
  rels.all fun v => wordTab n α αi β βi v == idT n

@[noinline, expose] def vecRelCheck (D : CFSG.Sporadic.SmallF2.Native.VecData)
    (rels : List (List (Nat × Bool))) : Bool :=
  let O := D.orbit ()
  relCheck D.n O.alpha (invT D.n O.alpha) O.beta (invT D.n O.beta) rels

@[noinline, expose] def mclRelCheck (rels : List (List (Nat × Bool))) : Bool :=
  let O := CFSG.Sporadic.McL.Native.orbitData ()
  relCheck 275 O.alpha O.alpha O.beta (invT 275 O.beta) rels

@[noinline, expose] def heRelCheck (rels : List (List (Nat × Bool))) : Bool :=
  let O := CFSG.Sporadic.He.Native.orbitData ()
  relCheck 8330 O.alpha O.alpha O.beta (invT 8330 O.beta) rels

@[noinline, expose] def fi22RelCheck (rels : List (List (Nat × Bool))) : Bool :=
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  relCheck 3510 O.alpha O.alpha O.beta (invT 3510 O.beta) rels

@[noinline, expose] def j3RelCheck (D : CFSG.Sporadic.J3.Native.Data)
    (rels : List (List (Nat × Bool))) : Bool :=
  let cA := CFSG.Sporadic.J3.Native.transposeRows 80 D.rowsA
  let cB := CFSG.Sporadic.J3.Native.transposeRows 80 D.rowsB
  let pts := CFSG.Sporadic.J3.Native.orbitSorted 80 cA cB D.v0 D.n
  let pm := CFSG.Sporadic.J3.Native.posMap pts
  let tA := CFSG.Sporadic.J3.Native.imageTable 80 pm pts cA
  let tB := CFSG.Sporadic.J3.Native.imageTable 80 pm pts cB
  relCheck D.n tA (invT D.n tA) tB (invT D.n tB) rels

end CFSG.Sporadic.Bridge.TwoGen.Native
