module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs

public section

namespace CFSG.Sporadic.Recognition.SuzMultiplier

open CFSG.CosetTable

abbrev SuzIndexP1 : Prop :=
  (genSub {r : FreeGroup (Fin gcS) | r ∈ suzCover.map FreeGroup.mk}
      (subsetOf gcS [0, 1, 2, 3, 4, 6])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin gcS) | r ∈ suzCover.map FreeGroup.mk}
      (subsetOf gcS [0, 1, 2, 3, 4, 6])).index ≤ 5346

abbrev SuzIndexP2 : Prop :=
  (genSub {r : FreeGroup (Fin (subsetOf gcS [0, 1, 2, 3, 4, 6]).length) |
      r ∈ suzCover1.map FreeGroup.mk} (subsetOf _ [0, 1, 2, 3, 4])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin (subsetOf gcS [0, 1, 2, 3, 4, 6]).length) |
      r ∈ suzCover1.map FreeGroup.mk} (subsetOf _ [0, 1, 2, 3, 4])).index ≤ 416

abbrev SuzCardP2 : Prop :=
  Finite (PG _ suzCover2) ∧ Nat.card (PG _ suzCover2) ≤ 1209600

end CFSG.Sporadic.Recognition.SuzMultiplier

end
