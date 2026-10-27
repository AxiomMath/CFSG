module

public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def IsGreatestOrd (T M : Subgroup G) : Prop :=
  InM T M ∧ ∀ M₁ : Subgroup G, InM T M₁ → OrdLE T M₁ M

omit [Finite G] in
theorem le_of_ordLE_of_centralizer_le {T M M₁ : Subgroup G} (hle : OrdLE T M₁ M)
    (hC : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M) : M₁ ≤ M := by
  intro h hh
  obtain ⟨a, ha, c, hc, rfl⟩ := hle h hh
  refine M.mul_mem ha.2 (hC ?_)
  exact Subgroup.centralizer_le (le_conjClosure _ M₁) hc.2

theorem ne_mc_of_greatest {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsGreatestOrd T M) : M ≠ Mc := by
  rintro rfl
  obtain ⟨M₁, hM₁, hne⟩ := h.exists_inM_ne
  have hle : M₁ ≤ M := le_of_ordLE_of_centralizer_le (hM.2 M₁ hM₁) h.centralizer_le_mc
  exact hne (hM₁.1.2 M hM.1.1.1 hle).symm

end CFSG.Quasithin
