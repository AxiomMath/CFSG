module

public import CFSG.Monster.GMS.ASegUniqueness
public import CFSG.Monster.GMS.TableVOf
public import CFSG.Monster.Existence.MilestoneInputs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog

theorem orderOf_phiB_uBar'
    : orderOf (Existence.phiB Existence.uBar) = 2 :=
  (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid Existence.phiB Existence.uBar).trans
    Existence.orderOf_uBar

theorem nonempty_mulEquiv_autO_of_aseg
    (L : ASegLiterature)
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀)
    (hT : Triangulable (twoAGraph Existence.tGriess))
    (d₀ : B) (hd₀ : orderOf d₀ = 2) (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] (a z : G) (hG : GMSF1Type d₀ a z) :
    Nonempty (G ≃* CFSG.Monster.Griess.AutO) :=
  nonempty_mulEquiv_of_aseg_simple L (hSLS d₀ hd₀ hrank)
    (hSLS _ orderOf_phiB_uBar' Existence.rank_phiB_uBar_sub_one) hG
    Existence.gmsF1Type_MGriess_uncond hT
    (Existence.monster_existence_clauses_one_two_of_stroth hSLS).1.2.1

theorem aSegLiterature_of
    (hTB : TwoBabyUnique) (hTA : BabyTwoAAutInner)
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀) :
    ASegLiterature := by
  obtain ⟨-, -, -, -, -, hA, -⟩ := Existence.monster_existence_clauses_one_two_of_stroth hSLS
  have hB : IsTwoBabyCentralizer Existence.tGriess :=
    Existence.gmsF1Type_MGriess_uncond.1.isTwoBabyCentralizer
      (hSLS _ orderOf_phiB_uBar' Existence.rank_phiB_uBar_sub_one)
  exact
    { tableV := tableVStatement_of_model hTB hB (Existence.tableV_tGriess (hA _ (IsConj.refl _)))
      tableIII := Existence.babyTableIII
      tableIV := Existence.babyTableIV
      threeSwap := Existence.babyThreeSwap_of Existence.babyTableIII
      twoBabyUnique := hTB
      twoAAutInner := hTA }

theorem nonempty_mulEquiv_autO_of_three
    (hTB : TwoBabyUnique) (hTA : BabyTwoAAutInner)
    (hT : Triangulable (twoAGraph Existence.tGriess))
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀)
    (d₀ : B) (hd₀ : orderOf d₀ = 2) (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] (a z : G) (hG : GMSF1Type d₀ a z) :
    Nonempty (G ≃* CFSG.Monster.Griess.AutO) :=
  nonempty_mulEquiv_autO_of_aseg (aSegLiterature_of hTB hTA hSLS) hSLS hT d₀ hd₀ hrank G a z hG

end CFSG.Monster.GMS
