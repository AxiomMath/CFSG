module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalEmbedLinUni
public import CFSG.LocalAnalysis.StandardType.GGClassicalEmbedSymp
public import CFSG.LocalAnalysis.StandardType.GGClassicalEmbedOrth

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggClassicalProjEmbed_holds (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
      lab.tag = .twD) :
    LargeEvenLabelAll lab fun R _ I _ => GGClassicalProjEmbedAt (ggClassDeg lab) R I := by
  by_cases hl : GGClassLinUni lab
  · exact ggClassicalProjEmbed_linUni lab hlab hl
  · by_cases hs : lab.tag = .B ∨ lab.tag = .C
    · exact ggClassicalProjEmbed_symp lab hlab hs
    · refine ggClassicalProjEmbed_orth lab hlab ?_ hl
      unfold GGClassLinUni at hl
      tauto

end CFSG.StandardType

end
