module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoDCox
import CFSG.LocalAnalysis.StandardType.GGQTwoDRankFree
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPatterns

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

section Producer


theorem ggSecFivePhanDQTwoCell_of_inputs {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m)
    {cell : QTwoCell} (hRk1 : GGSecFiveRk1PhanInput) (hL1 : GGQTwoL1InputOn R)
    (hGen : GGQTwoGenInputOn R) (hCell : GGQTwoCellInputOn R cell)
    (hFar : GGQTwoFarInputOn R cell) : GGSecFivePhanDQTwoAtCell R cell := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' hm hM hsix hc
  refine Or.inr ?_
  have hcfg' : GGQTwoDCfg p B Bs x L D J 𝒦 M e := ⟨hcfg, ht, hs, hpres, hsix⟩
  have hm5 : 5 ≤ m := hR m hm
  obtain ⟨X, hfacts, hframe, -⟩ := hCell G p B Bs x L D J 𝒦 ι M e hcfg' m e' hm hM hc
  have hnode := qtwoNode_card_iso hRk1 hL1 hcfg' hM hm
  have h6 : ∀ i, Nat.card ↥(qtwoNode Bs (qtwoRefl e e') i) = 6 := fun i => (hnode i).1
  have horb : ∀ {T : Finset (Fin m)}, ((∃ i j, i ≠ j ∧ T = {i, j}) ∨
      (∃ i j k, ggCoxeterMatrixD m i j = 3 ∧ ggCoxeterMatrixD m j k = 3 ∧
        ggCoxeterMatrixD m i k = 2 ∧ T = {i, j, k})) → GGOrbAt X Bs e e' T :=
    fun hT => orbAt_of_frame_of_conj e hM hframe (qtwo_exists_conj_into_parab_pairA3 hm5 hT)
  have hpair : ∀ i j, ggCoxeterMatrixD m i j = 3 →
      UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (qtwoW Bs (qtwoRefl e e') i j)
        (qtwoNode Bs (qtwoRefl e e') i) (qtwoNode Bs (qtwoRefl e e') j) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      have h1 : ggCoxeterMatrixD m i i = 1 := (ggCoxeterMatrixD m).diagonal i
      omega
    exact qtwo_pair_of_orb hfacts hM h6 hij (horb (Or.inl ⟨i, j, hne, rfl⟩))
  obtain ⟨hcomm, hfar1⟩ :=
    ggQTwoRankFreeInput_holds G p B Bs x L D J 𝒦 ι M e hcfg' m e' (by omega) hM h6 hpair
  refine ⟨qtwoNode Bs (qtwoRefl e e'), qtwoW Bs (qtwoRefl e e'),
    qtwoSystem_of_nodes Bs (qtwoRefl e e') (fun i => (hnode i).2) hcomm hpair
      (hGen G p B Bs x L D J 𝒦 ι M e hcfg' m e' hm hM) ?_ hfar1
      (hFar G p B Bs x L D J 𝒦 ι M e hcfg' m e' hm hM hc)⟩
  intro i j k hij hjk hik
  exact qtwo_adjA3_of_orb hfacts hM h6 hij hjk hik
    (horb (Or.inr ⟨i, j, k, hij, hjk, hik, rfl⟩))

theorem ggQTwoFarInput_of_cell {cell : QTwoCell} (hP : QTwoParabConj)
    (hCell : GGQTwoCellInput cell) : GGQTwoFarInputOn (fun m => 7 ≤ m) cell := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc i k j l hik hjl hij hil hkj hkl
  obtain ⟨X, hfacts, hframe, -⟩ := hCell G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc
  exact qtwo_far2_of_orb hfacts hM hik hjl hij hil hkj hkl (orbAt_of_frame e hP hm hM hframe
    (Or.inr (Or.inr (Or.inr ⟨i, k, j, l, hik, hjl, hij, hil, hkj, hkl, rfl⟩))))

end Producer

end CFSG.StandardType.QTwo

end
