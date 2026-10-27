module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Quasithin

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem e22r_isSylowIn_of_le {p : ℕ} {P Q H : Subgroup G} (hP : IsSylowIn p P H) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) (hQ : IsPGroup p Q) : IsSylowIn p Q H := by
  refine ⟨hQH, hQ, fun h => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P Q H hPQ hQH]
  exact Dvd.dvd.mul_left h _

end CFSG.Quasithin.E22L2
