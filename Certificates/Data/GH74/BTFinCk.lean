module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates.BTFinCk

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def commCount (n : Nat) (L : Array Table) (w : Table) : Nat :=
  (List.range L.size).countP fun k => commT n L[k]! w

@[expose] def fourOK (n : Nat) (L : Array Table) (a : Table) (bound : Nat) : Bool :=
  allIn 0 L.size fun j =>
    !invoOK n L[j]! || tblEq n L[j]! (idT n) || tblEq n L[j]! a ||
      bound % commCount n L L[j]! == 0

@[expose] def centFourOK (n : Nat) (gens : List Table) (a : Table) (ord cap bound : Nat) :
    Bool :=
  let CL := mulClosureH n gens.toArray cap
  mulTreeOK n gens.toArray CL.1 CL.2.1 CL.2.2 && hkeysDistinct n CL.1.toList &&
    CL.1.size == ord && fourOK n CL.1 a bound

end Certificates.BTFinCk
