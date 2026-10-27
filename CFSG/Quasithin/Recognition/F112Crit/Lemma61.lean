module

public import CFSG.Quasithin.Recognition.F112Crit.Setting

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

variable {G : Type u} [Group G] [Finite G] {L₁ L₂ S : Subgroup G}

theorem P₁_le_normalizer (h : Hyp111R L₁ L₂ S) :
    P₁ L₁ L₂ S ≤ Subgroup.normalizer (L₁ : Set G) :=
  sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h).1

theorem lemma61_sylow (h : Hyp111R L₁ L₂ S) : IsSylowTwoOf S (P₁ L₁ L₂ S) :=
  F112W.isSylowTwoOf_parabolic h

theorem pCoreOf_P₁ (h : Hyp111R L₁ L₂ S) (hS : S ≤ L₁) :
    pCoreOf 2 (P₁ L₁ L₂ S) = pCoreOf 2 L₁ := by
  refine le_antisymm ?_
    (pCoreOf_mono_of_le_normalizer le_sup_left (P₁_le_normalizer h))
  have h1 : pCoreOf 2 (P₁ L₁ L₂ S) ≤ L₁ :=
    (isSylowTwoOf_pCoreOf_le (lemma61_sylow h)).trans hS
  exact fun x hx => pCoreOf_inf_le (le_sup_left : L₁ ≤ P₁ L₁ L₂ S) ⟨hx, h1 hx⟩

end CFSG.Quasithin.F112Crit
