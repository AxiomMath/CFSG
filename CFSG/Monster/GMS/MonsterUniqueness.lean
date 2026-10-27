module

public import CFSG.Monster.GMS.ASegMonster
public import CFSG.Monster.GMS.TwoAGraphIso
public import CFSG.Monster.GMS.TwoBabyUniqueOf
public import CFSG.Monster.Tri.ASegFactsLiterature
public import CFSG.Monster.Existence.MilestoneTableOne

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog CFSG.Monster.Generated
  CFSG.Monster.Tri.Leech

theorem triangulable_twoAGraph_tGriess_of
    (hTA : BabyTwoAAutInner)
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀)
    (hOT : OddTypeOrdersCF tStarG xmatG) (hTG : ThreeCGenerated tStarG xmatG) :
    Triangulable (twoAGraph Existence.tGriess) := by
  obtain ⟨⟨-, -, -, hcard⟩, -⟩ := Existence.monster_existence_clauses_one_two_of_stroth hSLS
  have I : GMSInterfaces (Existence.phiB Existence.uBar) Gmat :=
    (aSegLiterature_of twoBabyUnique hTA hSLS).interfaces
      (hSLS _ orderOf_phiB_uBar' Existence.rank_phiB_uBar_sub_one) Gmat
  have h := CFSG.Monster.Tri.twoAGraph_triangulable_Gmat_of_parts I Existence.babyLineOddOrder
    (Existence.babyFi22Slice_of Existence.babyTableIII) hOT hTG (IsConj.refl tStarG)
  exact (triangulable_twoAGraph_of_eq (Existence.Gmat_eq_AutO hcard) rfl).mp h

end CFSG.Monster.GMS
