module

public import CFSG.Quasithin.Vol2.KGFactC31HeData
public import CFSG.Sporadic.HeldB.Common

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Sporadic.HeldB

@[expose] noncomputable def gens3 : List (Equiv.Perm (Fin 8330)) :=
  [heGenPerm 0, heGenPerm 1, heAutU]

@[expose] noncomputable def elt (w : List ℤ) : Equiv.Perm (Fin 8330) := evalSignedWord gens3 w

@[expose] noncomputable def heE : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure (Set.range fun i : Fin 6 => elt (eW.getD i []))

@[expose] noncomputable def heQ : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure (Set.range fun i : Fin 4 => elt (qW.getD i []))

@[expose] noncomputable def nsGrp : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure (Set.range ![elt (nsW.getD 6 []), elt (nsW.getD 11 [])] ∪
    Set.range fun i : Fin 6 => elt (eW.getD i []))

@[expose] noncomputable def n7Grp : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure (Set.range ![elt (n7W.getD 3 []), elt (n7W.getD 9 [])] ∪
    Set.range fun i : Fin 4 => elt (qW.getD i []))

@[expose] noncomputable def lGrp : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {x | ∃ w ∈ lsGenW, elt w = x}

end CFSG.Quasithin.KGC31.He

end
