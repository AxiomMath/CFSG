module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_nbr {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {d : G}
    {N : Subgroup G} (hN : GGNbr p B x D J d N) : N ≤ Subgroup.centralizer ({d} : Set G) := by
  obtain ⟨⟨-, -, -, hle, -, -⟩, -⟩ := hN
  exact hle

end CFSG.StandardType

end
