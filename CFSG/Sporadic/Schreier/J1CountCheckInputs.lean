module

public import CFSG.Sporadic.Schreier.J1Tables
public import CFSG.Sporadic.Schreier.ClassSum
public meta import CFSG.Sporadic.Schreier.J1Tables
public meta import CFSG.Sporadic.Schreier.ClassSum

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def j1ATbl : Table := listTbl 3080 j1A1List

@[expose] def j1BTbl : Table := listTbl 3080 j1A2List

@[expose] def j1AInvTbl : Table := invT 3080 j1ATbl

@[expose] def j1BInvTbl : Table := invT 3080 j1BTbl

@[expose] def j1GenTbls : Array Table := #[j1ATbl, j1BTbl]

@[expose] def j1GenInvTbls : Array Table := #[j1AInvTbl, j1BInvTbl]

@[expose] def j1OrderTables (m : ℕ) : List Table :=
  filterProducts 3080 (ordTest 3080 m) j1Tables (idT 3080) []

end CFSG.Sporadic.Schreier
