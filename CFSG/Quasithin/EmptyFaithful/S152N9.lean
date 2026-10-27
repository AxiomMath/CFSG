module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152NBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique S152N

@[expose] def StagePair152 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      ∃ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂

variable {G : Type} [Group G] [Finite G]

theorem stageNotation15209_of_pair (h1519 : StageLemma1519) (h15112 : StageLemma15112)
    (h15208 : StageLemma15208) (hord : Input15209Order) (hpair : StagePair152) :
    StageNotation15209 := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hTsyl := isSylowTwoOf_hStar hs hH
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have h1519' := h1519 G T Mc M hs.qtfe hs.mf hs.ce
  refine ⟨((h1519'.three H hH).1.trans (h1519'.three H hH).2), (inf_eq_of_W3 hs hH φ).symm,
    (inf_eq_of_W3 hs hH φ).trans (inf_normalizer_eq_of_W3 hs hH φ).symm,
    relIndex_inf_eq_nine hs hH φ, hpair G T Mc M hs H hH, hord G T Mc M hs H hH, ?_⟩
  obtain ⟨A, hAΔ, hAT⟩ := exists_deltaSet_not_le hTsyl (exists_mem_deltaSet hTsyl hc.exists_A)
  have hord' := hord G T Mc M hs H hH A hAΔ
  refine ⟨A ⊓ pCoreOf 2 H, ⟨A, hAΔ, rfl⟩, ?_⟩
  rintro ⟨A', hA'Δ, hA'T, hAA'⟩
  have hA'max : IsMaxElemAbelian T A' :=
    ⟨hA'T, hA'Δ.1.2.1, fun B hBT hB => hA'Δ.1.2.2 B (hBT.trans hH.1.1) hB⟩
  have hJ : A' ≤ thompsonJ T := le_iSup₂_of_le A' hA'max le_rfl
  have h0 : ⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ = ⊥ := by
    rw [hAA']
    exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl (inf_le_left.trans hJ)).trans
      h1519'.one_commute.le)
  exact delta_commutator_ne_bot hs hH φ hc hAΔ hord' hAT h0

end CFSG.Quasithin
