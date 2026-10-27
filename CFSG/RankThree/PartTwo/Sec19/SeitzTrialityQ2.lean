module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Planes
public import Certificates.Certificate188007
public import Certificates.Certificate188008

public section

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.AGLEmbedding.ChevOuter

namespace CFSG.RankThree.PartTwo.Sec19

@[expose] def TwoChecks : Prop :=
  HuppertD4Q2.planeCoverCheck () = true ∧ ∀ i < 6, HuppertD4Q2.classCheck i = true

theorem twoChecks_of_certs (h1 : HuppertD4Q2.planeCoverCheck () = true)
    (h2 : HuppertD4Q2.classChecks () = true) : TwoChecks :=
  ⟨h1, fun i hi => by
    simp only [HuppertD4Q2.classChecks, List.all_eq_true, List.mem_range] at h2
    exact h2 i hi⟩

theorem trialityTwoPlanes_of_checks (hc : TwoChecks)
    (hZ : Subgroup.center lineGroup = ⊥) (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312) :
    TrialityTwoPlanes :=
  TrialityTwo.trialityTwoPlanes_of_checks hZ hAut hc.1 hc.2

section Conclusion

set_option linter.unusedSectionVars false


theorem trialityThreeInnerTwo_of_checks (hc : TwoChecks) : TrialityThreeInnerTwo :=
  trialityThreeInnerTwo_of_planes fun hZ hAut => trialityTwoPlanes_of_checks hc hZ hAut

theorem trialityThreeOuterTwo_of_checks (hc : TwoChecks) : TrialityThreeOuterTwo :=
  trialityThreeOuterTwo_of_planes fun hZ hAut => trialityTwoPlanes_of_checks hc hZ hAut

theorem trialityThreeInnerTwo :
    TrialityThreeInnerTwo :=
  trialityThreeInnerTwo_of_checks
    (twoChecks_of_certs Certificates.certificate188007 Certificates.certificate188008)

theorem trialityThreeOuterTwo :
    TrialityThreeOuterTwo :=
  trialityThreeOuterTwo_of_checks
    (twoChecks_of_certs Certificates.certificate188007 Certificates.certificate188008)

end Conclusion

end CFSG.RankThree.PartTwo.Sec19
