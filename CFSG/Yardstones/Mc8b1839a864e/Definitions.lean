module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Yardstones.Mc8b1839a864e

@[expose] def FaithfulLocalNonemptyTauCetiStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.Quasithin.quasithinIsQTKE G → ∀ T : Sylow 2 G,
    (∃ L : Subgroup G, CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) →
      CFSG.Assembly.InCatalog G

end CFSG.Yardstones.Mc8b1839a864e
