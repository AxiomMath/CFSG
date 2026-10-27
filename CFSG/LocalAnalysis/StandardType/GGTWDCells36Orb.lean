module

public import CFSG.LocalAnalysis.StandardType.GGTWDRes

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWDE6Orbit (S : Set (Module.End (ZMod 3) (GGDepAE 3 6))) : Prop :=
  ∃ (s : Fin 6 → Module.End (ZMod 3) (GGDepAE 3 6))
      (w : Fin 72 → Module.End (ZMod 3) (GGDepAE 3 6)),
    (∀ i, ∃ c f : GGDepAE 3 6, ggDepAdot f c = 2 ∧ s i = ggDepARefl c f) ∧
    (∀ i, s i ∈ Submonoid.closure S) ∧ (∀ g ∈ S, g ∈ Submonoid.closure (Set.range s)) ∧
    (∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆.M i j) = 1) ∧
    (∀ k, w k ∈ Submonoid.closure S) ∧ Function.Injective fun k => w k (ggDepAx 3 6)

@[expose] def GGTWDCells36Orb : Prop :=
  GGTWDCellsOr 3 6 GGTWDE6Orbit

end CFSG.StandardType

end
