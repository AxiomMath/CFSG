module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP14

open Matrix

@[expose] def IsTransvectionGL {n : ℕ} (t : GL (Fin n) (ZMod 3)) : Prop :=
  t ≠ 1 ∧ ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1) * ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1)
    = 0 ∧ ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1).rank = 1

@[expose] def SylowTransvectionGL43 : Prop :=
  ∀ W : Subgroup (GL (Fin 4) (ZMod 3)), CFSG.RankThree.SubgroupLists.IsIrreducibleOn W →
    (∃ t ∈ W, IsTransvectionGL t) → ∀ P : Sylow 3 W, ∃ t ∈ P,
      IsTransvectionGL (t : GL (Fin 4) (ZMod 3))

end CFSG.RankThree.PartTwo.KFacts.KP14
