module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenterJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenterU33
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenterG2
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

@[expose] def G2SylowCenterWeakClosure : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r ≠ 3 →
    CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterWeaklyClosed Y

@[expose] def G2CharThreeInversion : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ),
    CFSG.Blueprint.LieModel Y .G2 0 3 f → SylowCenterInverted Y

theorem sylowCenterInverted_inputs
    (hH2 : G2CharThreeInversion) :
    (∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .J2 → SylowCenterInverted Y) ∧
    (∀ (Y : Type) [Group Y] [Finite Y],
      CFSG.Blueprint.LieModel Y .PSU 3 3 1 → SylowCenterInverted Y) ∧
    (∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime →
      CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterInverted Y) := by
  refine ⟨fun Y _ _ h => sylowCenterInverted_of_isSpor_j2 h,
    fun Y _ _ h => sylowCenterInverted_of_lieModel_psu3 h, fun Y _ _ r f _ h => ?_⟩
  by_cases hr3 : r = 3
  · subst hr3
    exact hH2 Y f h
  · exact sylowCenterInverted_of_lieModel_g2 hr3 h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
