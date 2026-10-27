module

public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def inSpan (n : Nat) (bs : List Table) (t : Table) : Bool :=
  (spanTabs n bs).any (tblEq n t)

@[expose] def elabOK (n : Nat) (gs : List Table) : Bool :=
  (gs.all fun g => tblEq n (compT n g g) (idT n)) && gs.all fun g => gs.all fun h => commT n g h

@[expose] def frameCheck (n m : Nat) (x : Table) (ub vs : List Table)
    (cands : List (List Table)) : Bool :=
  invOK n x (invT n x) && vs.all fun v =>
    inSpan n ub v || !(elabOK n (ub ++ orbTabs n m x (invT n x) v)) ||
      cands.any (orbIs n (ub ++ orbTabs n m x (invT n x) v))

@[expose] def blocksOK (bl : List (List Nat)) (g : Table) : Bool :=
  bl.all fun T => bl.any fun T' => T.all fun p => T'.contains (ap g p)

@[expose] def fixesBlocks (bl : List (List Nat)) (g : Table) : Bool :=
  bl.all fun T => T.all fun p => T.contains (ap g p)

end CFSG.Quasithin.KGC31.Native

end
