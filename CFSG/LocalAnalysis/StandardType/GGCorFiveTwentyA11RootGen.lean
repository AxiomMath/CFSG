module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11NbrOn
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggCorFiveTwentyA11CfgRootGenLInput_of_row (hRig : GGLabelRigidInput)
    (hKG : GGRootGenKGAvoidOn GGTypeALabel) : GGCorFiveTwentyA11CfgRootGenLInput := by
  intro G _ _ p B Bs x L D J hHyp _ hA
  obtain ⟨rfl, hmod, -⟩ := hA
  have hmod' : Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (3 + 1) 2 3 := hmod
  refine ggRootCompGenAvoiding_L_of_avoidOn hKG hHyp (largeEvenMarking_mono ?_
    (ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 (largeEvenInLambda2_typeA hmod')
      (ggHasLabel_typeA hmod')))
  rintro lab R _ I F θ ⟨rfl, hP⟩
  exact ⟨Or.inl ⟨rfl, by decide, by decide⟩, hP⟩

theorem ggCorFiveTwentyA11CfgRootGenNbrInputOn_of_row {S : ℕ → LargeEvenLabel → Prop}
    (hKG : GGRootGenKGAvoidOn S) : GGCorFiveTwentyA11CfgRootGenNbrInputOn S := by
  intro G _ _ p B Bs x L D J hHyp _ _ y K hnb hK
  exact ggRootCompGenAvoiding_nbr_of_avoidOn hKG hHyp hnb hK

end CFSG.StandardType

end
