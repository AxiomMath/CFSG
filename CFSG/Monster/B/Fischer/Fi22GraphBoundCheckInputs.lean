
module

public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Basic
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def fi22N0List : List ℕ :=
  (List.range 3510).filter fun i => i != 0 && ((fi22OuterStrong3510 1)[0]!)[i]! == i

@[expose] def fi22Nbr : Array (List ℕ) := adjSearch 3510 fi22OrigArrs fi22N0List

@[expose] def fi22Colour (s : ℕ) : Array ℕ :=
  refineIter 3510 fi22Nbr (individualize 3510 fi22GraphBase s) 4

@[expose] def fi22ClassCount (c : Array ℕ) (v : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 3510 => c[w.val]! = c[v]!).card

end CFSG.Monster.B.Fischer
