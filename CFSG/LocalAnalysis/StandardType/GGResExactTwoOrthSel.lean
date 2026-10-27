module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmallDefs
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProper
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmall
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrthEnd
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndMain
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggResExactTwoOrthSelLeaf_holds :
    GGResExactTwoOrthSelLeaf := by
  intro hRig G _ _ p B Bs x L D J hcfg hlab hne
  obtain ⟨lab0, hlabΛ0, hhas0, R0, _, I0, F0, θ0, hP0⟩ := largeEvenMarking_exists_hasLabel hlab
  have hp3 : p = 3 := hP0.1.1
  have hp : p.Prime := by rw [hp3]; norm_num
  have hlab' : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 4 ≤ lab.rank) p Bs L :=
    GGInnerDiagOnLabel.mono' (fun lab h => ⟨h.1, Or.inr h.2.1, h.2.2.1, by omega⟩) hlab
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    (ggResExactTwoOrth_card_bstar_inf_L hRig hcfg hlab').2
  have hM : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .twD ∧ lab.n = 1 ∧
      lab.rank = 5) p B L :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨hP.1, fun b hb => hP.2.1 (hcfg.2.1.1 hb), fun b hb => hP.2.2 b (hcfg.2.1.1 hb)⟩) hlab
  have hlabel : ∀ lab, LargeEvenInLambda2 lab →
      (fun p lab => p = 3 ∧ lab.tag = .twD ∧ lab.n = 1 ∧ lab.rank = 5) p lab →
      LargeEvenLabelAll lab (fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGEndNodeIOneNonSmall p r R I) := by
    intro lab hlabΛ hS
    have hE : GGIOneMoreOrthEnnolaLabel p lab := by
      have hn : lab.n = 1 := hS.2.2.1
      have hr : lab.rank = 5 := hS.2.2.2
      have hp3' : p = 3 := hS.1
      refine Or.inl ⟨hS.2.1, by omega, by rw [hr]; decide, ?_, ?_⟩
      · rw [hp3', hn]; norm_num
      · rw [hp3', hn]; norm_num
    intro Q hQ
    obtain ⟨t, l, n⟩ := lab
    rcases hE with ⟨ht, hl, hlo, hpn, hpn'⟩ | ⟨ht, hl, hle, hn, hp3''⟩
    · dsimp only at ht hl hlo hpn hpn'
      subst ht
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      split_ifs at hQ ⊢ with h2 h3
      · omega
      · omega
      · obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
        exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, ggOutdiagOdd_innSet _ _, l - 1,
          ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc,
          ggEndNodeIOneNonSmall_orthMinus (m := l - 1) hK (by omega) hp hpn hpn' hbc⟩
    · exfalso
      dsimp only at ht hS
      rw [ht] at hS
      exact absurd hS.2.1 (by decide)
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => p = 3 ∧ lab.tag = .twD ∧
      lab.n = 1 ∧ lab.rank = 5) hlabel (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hPmark, hP'⟩ := hP
  obtain ⟨-, hBN, h3⟩ := hPmark
  obtain ⟨hOD, r, hlift, hend⟩ := hP' 
  obtain ⟨D₁, K₁, hstd, hns⟩ :=
    exists_stdSubPre_nonSmall_of_data hcfg.1 hcfg.2.1 hne hnc hL θ hBN h3 hOD hlift hend
  exact ⟨D₁, K₁, hstd, hns hp3⟩

end CFSG.StandardType
