module

public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def cosetOK (n : Nat) (b : Table) (bs rs : List Table) : Bool :=
  rs.length + 1 == 2 ^ bs.length &&
    (List.range rs.length).all fun m =>
      invOK n (rs.getD m (idT n)) (invT n (rs.getD m (idT n))) &&
        tblEq n (conjTab n (rs.getD m (idT n)) (invT n (rs.getD m (idT n))) b)
          (maskProd n bs (m + 1))

@[expose] def cosetCount (n : Nat) (cb rs : List Table) (f : Table → Bool) : Nat :=
  (rs.map fun r => cb.countP fun c => f (compT n r c)).sum

@[expose] def fixesAll (g : Table) (pts : List Nat) : Bool := pts.all fun i => ap g i == i

@[expose] def fixSetIs (n : Nat) (bs : List Table) (pts : List Nat) : Bool :=
  (List.range n).all fun i => (bs.all fun b => ap b i == i) == pts.contains i

end CFSG.Quasithin.KGC31.Native

end
