module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Exist
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Six

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt15412_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (h8 : Stmt1548 G T)
    (h11 : Stmt15411 G T) : Stmt15412 G T := by
  intro M hM
  have hS := L15412.setup_of hyp h2 h8 h11 hM
  refine ⟨hS.exists_mem, fun Y hY hYM => ?_⟩
  have heq := hS.eq_normalizer hY hYM
  have huniq : IsUniqueM (Y ⊔ T) M := by
    refine ⟨⟨hM.1, sup_le hYM hM.2⟩, fun M' hM' => ?_⟩
    have hS' := L15412.setup_of hyp h2 h8 h11 ⟨hM'.1, le_sup_right.trans hM'.2⟩
    exact (hS'.eq_normalizer hY (le_sup_left.trans hM'.2)).trans heq.symm
  obtain ⟨s, hs, hidx, hcube, hU, hUJ⟩ := hS.three hY hYM
  obtain ⟨hsyl, h5⟩ := hS.five hY hYM
  refine ⟨hS.le_normalizer_of_mem hY hYM, heq, huniq, ⟨s, hs, hidx, hcube, hU⟩, hsyl, h5, ?_,
    ⟨T, hS.minParabolic hY hYM⟩⟩
  obtain ⟨𝓗, I, B, hI2⟩ := hS.exists_blocks
  rcases hS.classify B hI2 hY hYM with ⟨L, -, f, -, hf3, hD, -⟩ |
    ⟨L₁, hL₁, L₂, hL₂, h12, hI', f₁, hf₁, f₂, hf₂, h3₁, h3₂, hD, x, hx, hxL⟩
  ·
    have hidx3 : (CFSG.Open.pCoreOf 2 Y).relIndex Y = 3 := by
      rw [L15412.relIndex_pCoreOf_eq hS.elem (hYM.trans hS.le_normalizer)
        (hS.odd_card_autI hY hYM) (hS.isPGroup_inf' hYM), hD, Nat.card_zpowers, hf3]
    have hs1 : s = 1 := by
      rcases hs with rfl | rfl
      · rfl
      · rw [hidx3] at hidx
        norm_num at hidx
    rw [hs1] at hU hUJ
    exact hS.six_one hY hYM hidx3 (by rw [hU, pow_one])
      (by rw [hS.relIndex_eCentOf hY hYM hUJ, pow_one])
  ·
    exact hS.six_two hY hYM B hL₁ hL₂ h12 hI' hf₁ hf₂ h3₁ h3₂ hD hx hxL

end CFSG.Quasithin.EmptyFaithfulMultiple
