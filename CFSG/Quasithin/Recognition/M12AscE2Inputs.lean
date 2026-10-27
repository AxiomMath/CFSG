module

public import CFSG.Quasithin.Recognition.M12AscE1
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open Subgroup Equiv

variable {G : Type*} [Group G] {z : G}

@[expose] def sig3 : Perm (Fin 6) := swap 3 4 * swap 2 3

end CFSG.Quasithin
