module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCompLabCat
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import Certificates.Certificate707002
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafCells

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem e6TwoLeaf_knownOverSix_W :
    KnownOverSix (E6SmallOn 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hD
    obtain ⟨hDat, _⟩ := hD
    exact kg5a_exc hX (e6TwoLeaf_datumOn_mono (fun t ht => Or.inl ht) hDat)
  · intro X _ _ hX A δ J hD hJ hcent
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hW, hcent'⟩ := e6TwoLeaf_label_W hDat hsmall
    exfalso
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ := hJ
    have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawJ
    have hpropJ : GGLabelA2 labJ :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawJ)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labJ lab' := hrigid labJ lab' _ hlabJ hlab' hHasJ hhas'
    have hEq : labJ = lab' := e6TwoLeaf_A2_rigid hIso hpropJ
    exact (hcent' (e6TwoLeaf_W_of_A2 hW (hEq ▸ hpropJ))) hcent
  · intro X _ _ hX A δ J hD hJ hz
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hW, -⟩ := e6TwoLeaf_label_W hDat hsmall
    exfalso
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ := hJ
    have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawJ
    have hpropJ : GGLabelA2 labJ ∧ labJ.tag = .twA :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawJ)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labJ lab' := hrigid labJ lab' _ hlabJ hlab' hHasJ hhas'
    have hEq : labJ = lab' := e6TwoLeaf_A2_rigid hIso hpropJ.1
    exact e6TwoLeaf_false_W_of_twA2 hIso ⟨hpropJ.2, hpropJ.1.1⟩ hW
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hW, -⟩ := e6TwoLeaf_label_W hDat hsmall
    exfalso
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ := hJ
    have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawJ
    have hpropJ : labJ.tag = .triD4 :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawJ)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labJ lab' := hrigid labJ lab' _ hlabJ hlab' hHasJ hhas'
    exact e6TwoLeaf_false_W_of_triD4 hIso hpropJ hW
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hW, -⟩ := e6TwoLeaf_label_W hDat hsmall
    exfalso
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ := hJ
    have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawJ
    have hpropJ : labJ.tag = .D ∧ labJ.rank = 4 ∧ Odd labJ.n :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawJ)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labJ lab' := hrigid labJ lab' _ hlabJ hlab' hHasJ hhas'
    exact e6TwoLeaf_false_W_of_D4 hIso ⟨hpropJ.1, hpropJ.2.1⟩ hW
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hW, -⟩ := e6TwoLeaf_label_W hDat hsmall
    exfalso
    obtain ⟨-, labJ, hlabJ, hrawJ⟩ := hJ
    have hHasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawJ
    have hpropJ : labJ.tag = .A ∧ labJ.rank = 1 :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawJ)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labJ lab' := hrigid labJ lab' _ hlabJ hlab' hHasJ hhas'
    exact e6TwoLeaf_false_W_of_A1 hIso hpropJ.1 hpropJ.2 hW

private theorem e6TwoLeaf_knownOverSix_T
    (hZ : TwE6A2CentreInputTwo) : KnownOverSix (E6SmallOn 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hD
    obtain ⟨hDat, _⟩ := hD
    exact kg5a_exc hX (e6TwoLeaf_datumOn_mono (fun t ht => Or.inr (Or.inl ht)) hDat)
  · intro X _ _ hX A δ J hD hJ hcent
    obtain ⟨hDat, _⟩ := hD
    have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
      e6TwoLeaf_datumOn_mono (fun t ht => Or.inr ht) hDat
    refine ggMarkingAll_mono (fun lab R _ I F θ h hs => ?_)
      (e6eps_marking_labels hX hD6 (e6TwoLeaf_marking_E6_deg hDat))
    rcases h hs with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro X _ _ hX A δ J hD hJ hz
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hT⟩ := e6TwoLeaf_label_T hDat hsmall
    have hJperf : commutator J = ⊤ := hJ.1
    exfalso
    obtain ⟨-, lab0, hlab0, hraw0⟩ := hJ
    have hHas0 : GGHasLabel lab0 (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
    have hprop0 : GGLabelA2 lab0 ∧ lab0.tag = .twA :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hraw0)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso lab0 lab' := hrigid lab0 lab' _ hlab0 hlab' hHas0 hhas'
    have hEq0 : lab0 = lab' := e6TwoLeaf_A2_rigid hIso hprop0.1
    have hEq3 : lab' = ⟨.twA, 2, 3⟩ :=
      e6TwoLeaf_eq_twA2_of_T hT
        ⟨by rw [← hEq0]; exact hprop0.2, by rw [← hEq0]; exact hprop0.1.1⟩
    have hn0 : lab0.n = 3 := by rw [hEq0, hEq3]
    have hJmark3 : LargeEvenMarking J (fun lab _ _ _ _ _ =>
        lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3) := by
      refine ⟨hJperf, lab0, hlab0, ?_⟩
      refine largeEvenRawDatum_mono ?_ hraw0
      rintro R _ I F ⟨hs, hna, θ, hg, ht⟩
      exact ⟨hs, hna, θ, ht, hg.1, hn0⟩
    exact hz (e6TwoLeaf_center_of_tableZ hZ hDat hsmall hJmark3)
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, _⟩ := hD
    have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
      e6TwoLeaf_datumOn_mono (fun t ht => Or.inr ht) hDat
    refine ggMarkingAll_mono (fun lab R _ I F θ h hs => ?_)
      (e6eps_marking_labels hX hD6 (e6TwoLeaf_marking_E6_deg hDat))
    exact h hs
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, _⟩ := hD
    have hD6 : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J :=
      e6TwoLeaf_datumOn_mono (fun t ht => Or.inr ht) hDat
    refine ggMarkingAll_mono (fun lab R _ I F θ h hs => ?_)
      (ggMarkingAll_and (e6eps_marking_labels hX hD6 (e6TwoLeaf_marking_E6_deg hDat))
        (e6TwoLeaf_marking_tag hX hDat))
    obtain ⟨h1, h2⟩ := h
    rcases h1 hs with hE6 | htw
    · exact absurd (hE6.1.symm.trans (h2 hs)) (by decide)
    · exact Or.inl htw
  · intro X _ _ hX A δ J hD hJ
    obtain ⟨hDat, hsmall⟩ := hD
    obtain ⟨lab', hlab', hhas', hT⟩ := e6TwoLeaf_label_T hDat hsmall
    exfalso
    obtain ⟨-, labA, hlabA, hrawA⟩ := hJ
    have hHasA : GGHasLabel labA (↥J ⧸ Subgroup.center ↥J) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawA
    have hpropA : labA.tag = .A ∧ labA.rank = 1 :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawA)
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labA lab' := hrigid labA lab' _ hlabA hlab' hHasA hhas'
    exact e6TwoLeaf_false_T_of_A1 hIso hpropA.1 hpropA.2 hT

theorem leafE6Two_holds :
    KnownOverSix (E6SmallOn 5) ∧ (TwE6A2CentreInputTwo → KnownOverSix (E6SmallOn 6)) := by
  exact ⟨e6TwoLeaf_knownOverSix_W, fun hZ => e6TwoLeaf_knownOverSix_T hZ⟩

end CFSG.StandardType.TablePThreeKG

end
