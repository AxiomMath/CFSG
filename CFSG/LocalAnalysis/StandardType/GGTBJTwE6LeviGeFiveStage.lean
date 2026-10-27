module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviGeFive
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJLeftOnLab_twE6_geFive
    (hRig : GGLabelRigidInput) : GGTBJLeftOnLab ggTBJTwE6LabelGeFive := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp5, h3, -⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hL' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hL
  have hnc : ¬ (ggTBJTwE6RowCand p n labJ ∨ ¬ (5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1)) := by
    rintro (h | h)
    · rcases h with ⟨-, -, hp3, -⟩ | ⟨-, hp3, -⟩ | ⟨-, -, hp3, -⟩ <;> omega
    · exact h ⟨hp5, h3⟩
  exact (ggTBJTwE6LeviL_geFive hRig G p B Bs x L D J y K hH hL' hX n hΛ hhas hreg labJ hΛJ hhasJ
    hdvd hnc).imp id Or.inl

theorem ggTBJNbrOnLab_twE6_geFive
    (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) :
    GGTBJNbrOnLab ggTBJTwE6LabelGeFive := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp5, h3, -⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hK' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hK
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1
  have hnc : ¬ (ggTBJTwE6RowCand p n labJ ∨ ¬ (5 ≤ p ∧ ¬ 3 ∣ 2 ^ n + 1)) := by
    rintro (h | h)
    · rcases h with ⟨-, -, hp3, -⟩ | ⟨-, hp3, -⟩ | ⟨-, -, hp3, -⟩ <;> omega
    · exact h ⟨hp5, h3⟩
  exact (ggTBJTwE6LeviK_geFive hRig G p B Bs x L D J y K hH hJK hK' hX n hΛ hhas hreg labJ hΛJ
    hhasJ hdvd hnc).imp id Or.inl

theorem ggTBJLeftOn_twE6_geFive
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) : GGTBJLeftOn ggTBJTwE6LabelGeFive :=
  (ggTBJLeftOnLab_twE6_geFive hRig).toLeftOn hTCJ

theorem ggTBJNbrOn_twE6_geFive
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) :
    GGTBJNbrOn ggTBJTwE6LabelGeFive :=
  (ggTBJNbrOnLab_twE6_geFive hI3 hRig).toNbrOn hTCJ hI3

theorem GGTBJOrdinaryOutside.of_twE6_geFive
    {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hRig : GGLabelRigidInput)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJTwE6LabelGeFive p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_twE6_geFive hTCJ hRig)
    (ggTBJNbrOn_twE6_geFive hTCJ hI3 hRig) h

end CFSG.StandardType

end
