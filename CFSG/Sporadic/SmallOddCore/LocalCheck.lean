module

public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def wordTbl (n : Nat) (gs : List Table) (w : List Nat) : Table :=
  w.foldl (fun acc l => compT n acc (gs.getD (l - 1) (idT n))) (idT n)

@[expose] def enumOK (n cap m : Nat) (gs : List Table) : Bool :=
  let A := gs.toArray
  let E := mulClosureH n A cap
  gs.all (fun g => invOK n g (invT n g)) && mulTreeOK n A E.1 E.2.1 E.2.2 &&
    closedOK n (A ++ A.map (invT n)) E.1 && hkeysDistinct n E.1.toList && E.1.size == m

@[expose] def normOK (n cap : Nat) (gs cs : List Table) : Bool :=
  let E := mulClosureH n gs.toArray cap
  cs.all fun c => E.1.all fun x => memT n E.1 (conjT n c (invT n c) x)

@[expose] def centCount (n cap : Nat) (cs gs : List Table) : Nat :=
  (mulClosureH n cs.toArray cap).1.toList.countP fun y => gs.all fun g => commTT n y g

end CFSG.Sporadic.SmallOddCore
