module

public import CFSG.Quasithin.EmptyFaithful.S14113Stage
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_inf_ne_pCoreOf (h113 : StageLemma14113) {T Mc M₂ M₃ : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM₂ : InM T M₂) (hM₃ : InM T M₃) (hne : M₂ ≠ M₃) :
    pCoreOf 2 (M₂ ⊓ M₃) ≠ pCoreOf 2 M₂ := by
  intro hR
  have hTH : T ≤ M₂ ⊓ M₃ := le_inf hM₂.2 hM₃.2
  have hR1 : pCoreOf 2 (M₂ ⊓ M₃) ≠ ⊥ := by
    rw [hR]
    exact pCoreOf_ne_bot_of_isTwoLocal hM₂.1.1
  have hcgs : cgsIn M₃ (pCoreOf 2 (M₂ ⊓ M₃)) ≤ M₂ ⊓ M₃ := by
    rw [hR]
    have := cgsIn_pCoreOf_le hM₂.1 M₃
    rwa [inf_comm] at this
  rcases h113 G T Mc h M₃ (M₂ ⊓ M₃) hM₃ hTH inf_le_right hR1 hcgs with ⟨-, h1⟩ | ⟨-, -, hu⟩
  · exact hne (eq_of_pCoreOf_eq_of_isMaxTwoLocal hM₂.1 hM₃.1 (hR.symm.trans h1))
  · exact hne (hu.2 M₂ ⟨hM₂.1, inf_le_left⟩)

theorem lemma_14_1_14 (h113 : StageLemma14113) {T Mc M M₁ : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hM₁ : InM T M₁) (hne : M₁ ≠ M) :
    pCoreOf 2 M < pCoreOf 2 (M₁ ⊓ M) ∧ pCoreOf 2 M₁ < pCoreOf 2 (M₁ ⊓ M) := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hSM₁ : (S : Subgroup G) ≤ M₁ := hS ▸ hM₁.2
  refine ⟨lt_of_le_of_ne ?_ ?_, lt_of_le_of_ne ?_ ?_⟩
  · rw [inf_comm]
    exact pCoreOf_le_pCoreOf_inf_of_sylow hSM hSM₁
  · rw [inf_comm]
    exact fun heq => pCoreOf_inf_ne_pCoreOf h113 h hM hM₁ hne.symm heq.symm
  · exact pCoreOf_le_pCoreOf_inf_of_sylow hSM₁ hSM
  · exact fun heq => pCoreOf_inf_ne_pCoreOf h113 h hM₁ hM hne heq.symm

end CFSG.Quasithin
