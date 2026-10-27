module

public import CFSG.Quasithin.EmptyFaithful.S153E52G
public import CFSG.Quasithin.EmptyFaithful.S153E51B
public import CFSG.Quasithin.EmptyFaithful.S153E52C
public import CFSG.Quasithin.EmptyFaithful.S153E52E
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Fifty2H

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_52 (h113 : StageLemma14113) (h09 : Input15309Two) (i52 : Input15352)
    (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) : Concl15352 cx := by
  by_contra hna
  have hab : ∀ a ∈ UH153 T M V₁ Mc, ∀ b ∈ UH153 T M V₁ Mc, a * b = b * a := by
    intro a ha b hb
    by_contra hne
    exact hna ⟨a, ha, b, hb, hne⟩
  have hUS := le_S_of_abelian cx hab
  obtain ⟨-, -, -, hZS⟩ := case_b cx h51.one hUS
  have h4 := card_tildeU_eq_four i52 cx h51.one hZS
  have h8 := card_U_eq_eight cx h4
  have hCU := inf_centralizer_U_eq_ZS cx h51.one h8
  have hAV := commutator_pCoreY_Y_le cx h51.three (commutator_pCoreY_U_le cx hCU)
  have hAle := pCoreOf_Y_le_V h113 cx hAV
  exact absurd (h09 G T Mc M cx.c.hyp) (not_lt_of_ge hAle)

end Fifty2H

end S153E

end CFSG.Quasithin
