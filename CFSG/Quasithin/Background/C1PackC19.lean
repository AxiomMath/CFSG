module

public import CFSG.Quasithin.Background.C1PackQuasi
public import CFSG.Quasithin.Background.C1PackA4
public import CFSG.Quasithin.Background.C1CampbellConnect

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem distinctBlocksCommuteStatement {G : Type} [Group G] [Finite G] :
    DistinctBlocksCommuteStatement (G := G) := by
  intro H B₁ B₂ hH hB₁ hB₂ hne
  rcases hB₁.1.2.2.2.1 with hq₁ | h₁
  · exact C1Pack.commutator_eq_bot_of_quasisimple hB₁ hq₁ hB₂ hne
  · rcases hB₂.1.2.2.2.1 with hq₂ | h₂
    · rw [Subgroup.commutator_comm]
      exact C1Pack.commutator_eq_bot_of_quasisimple hB₂ hq₂ hB₁ hne.symm
    · exact C1Pack.commutator_eq_bot_of_card_three hH hB₁ h₁ hB₂ h₂ hne

theorem theoremC19 : TheoremC19 := fun _ _ _ => distinctBlocksCommuteStatement

end CFSG.Quasithin
