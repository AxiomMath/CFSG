module

public import CFSG.Quasithin.EmptyFaithful.S14114

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_14_1_15 (h113 : StageLemma14113) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) : IsUniqueM (oTwoFstarIn M ⊔ T) M := by
  refine ⟨⟨hM.1, sup_le (oTwoFstarIn_le M) hM.2⟩, fun M₁ hM₁ => ?_⟩
  by_contra hne
  have hM₁T : InM T M₁ := ⟨hM₁.1, le_sup_right.trans hM₁.2⟩
  have h1 := (lemma_14_1_14 h113 h hM hM₁T hne).1
  have hX : oTwoFstarIn M ≤ M ⊓ M₁ := le_inf (oTwoFstarIn_le M) (le_sup_left.trans hM₁.2)
  have h2 := a4_4_1 (pCoreOf_le_oTwoFstarIn M) hX (a44Hyp_oTwoFstarIn M)
  rw [inf_comm] at h1
  exact h1.ne h2.symm

end CFSG.Quasithin
