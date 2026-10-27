module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclE6
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclTwE6
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclE78
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclSmall
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclClassBig
public import CFSG.LocalAnalysis.StandardType.GGR4AmbExclClassSmall
public import Certificates.Certificate13657
public import Certificates.Certificate3951

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Ambient_of_excl
    (hM5 : GGClassicalTwoLocalRankNine) (hM10 : GGSmallThreeRank)
    (hM11 : GGE78TwoLocalRankSix) (hPD : GGProjDegreeF4) : GGR4AmbientLabel := by
  intro G _ _ B Bs x L D J hCfg hInner hCard hFact Γ _ _ C V _ _ ι φ h α hD hF4 hGen
  have hmark := GGInnerDiagOn.label (fun _ lab =>
    lab.tag = .F4 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) 3 hInner
  have hsplit : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .F4 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) ∨
        (GGR4ClassBig lab ∨ (GGR4ClassSmall lab ∨ ((lab.tag = .G2 ∨ lab.tag = .triD4 ∨
          lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
          lab.tag = .twF4der) ∨ ((lab.tag = .E7 ∨ lab.tag = .E8) ∨
          ((lab.tag = .E6 ∧ ¬ 3 ∣ 2 ^ lab.n + 1) ∨
            (lab.tag = .twE6 ∧ ¬ 3 ∣ 2 ^ lab.n - 1))))))) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨?_, hP.2⟩) hmark
    rcases lab with ⟨t, l, n⟩
    cases t <;> simp only [GGR4ClassBig, GGR4ClassSmall, reduceCtorEq, false_and, false_or,
      or_false, true_or, or_true, true_and, and_true, not_false_eq_true, and_self, forall_const] <;>
      first | tauto | skip
  rcases hsplit.elim_or with hS | h1
  · exact hS
  exfalso
  rcases h1.elim_or with h2 | h1
  · exact ggR4AmbExcl_classBig hM5 G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h2
  rcases h1.elim_or with h3 | h1
  · exact ggR4AmbExcl_classSmall hPD G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h3
  rcases h1.elim_or with h4 | h1
  · exact ggR4AmbExcl_small hM10 G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h4
  rcases h1.elim_or with h5 | h1
  · exact ggR4AmbExcl_E78 hM11 G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h5
  rcases h1.elim_or with h6 | h7
  · exact ggR4AmbExcl_E6 G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h6
  · exact ggR4AmbExcl_twE6 G B Bs x L D J hCfg hInner hCard Γ C V ι φ h α hD hF4 hGen h7

end CFSG.StandardType

end
