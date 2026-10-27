module

public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.SzF53A2
public import CFSG.Quasithin.EmptyFaithful.F112F53Res

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem f53AmalgamStatement_iff_noE : F53AmalgamStatement ↔
    ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
      ∀ E : Subgroup G, ¬ F53EData H S E := by
  constructor
  · intro h G _ _ H M S hA E hE
    have h64 := h G H M S hA E hE
    have h256 := F53EData.card_ge hA.quot_left hA.amalgam.sylow₁.1 hE
    omega
  · intro h G _ _ H M S hA E hE
    exact absurd hE (h G H M S hA E)

theorem input15208F53Res_of_amalgam (h : F53AmalgamStatement) : Input15208F53Res := by
  intro G _ _ L₁ L₂ S hyp hq h₁ h₂ h₃ _ E hES hab hnorm hchief hshape
  exact h G (L₂ ⊔ S) (L₁ ⊔ S) S (F53Amalgam.of_hyp111 hyp hq h₁ h₂ h₃) E
    ⟨hES, hab, hnorm, hchief, hshape⟩

end CFSG.Quasithin
