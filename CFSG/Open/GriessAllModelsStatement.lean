module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Models

public section

namespace CFSG.Open

abbrev GriessAllModelsStatement : Prop :=
  ∀ (X : Type) [Group X] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
    CFSG.Models.LieModel X t n p f →
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃*
        CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f)

end CFSG.Open
