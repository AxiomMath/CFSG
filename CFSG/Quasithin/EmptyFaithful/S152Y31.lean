module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input15205Hard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ M₁ : Subgroup G, InM T M₁ → M₁ = M ∨ M₁ = Mc

theorem stageLemma15205_of (hHard : Input15205Hard) : StageLemma15205 := by
  intro G _ _ T Mc M hs M₁
  refine ⟨hHard G T Mc M hs M₁, ?_⟩
  rintro (rfl | rfl)
  · exact hs.mf.1.1
  · exact hs.qtfe.inM_mc

end CFSG.Quasithin
