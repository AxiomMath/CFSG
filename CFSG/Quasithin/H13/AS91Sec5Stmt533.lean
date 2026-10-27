module

public import CFSG.Quasithin.H13.AS91Sec5PlaneCount

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

theorem stmt5_3_3_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c))
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (h54 : Stmt5_4) : Stmt5_3_3 := by
  intro G _ _ z hJ c a ha m hm ham
  obtain ⟨ρ⟩ := hres G z hJ c
  exact ρ.all_or_three_of_lnP hLU hG2 h54 hJ ha hm ham

end CFSG.Quasithin.H13.AS91
