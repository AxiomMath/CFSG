module

public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

namespace F617

open CFSG.Quasithin.F6

theorem isL2_of_lieModel_PSL_two {p f : ℕ} {G : Type} [Group G]
    (h : CFSG.Blueprint.LieModel G .PSL 2 p f) : IsL2 p f G := by
  rcases h with ⟨-, h'⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h'
  all_goals exact absurd h0 (by norm_num)

end F617

end CFSG.Quasithin
