module

public import CFSG.Monster.GMS.MonsterUniqueness
public import CFSG.Monster.GMS.BabyTwoAAutBridge
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueFinal
public import CFSG.Monster.Tri.OddTypeOrdersGmat

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog CFSG.Monster.Generated
  CFSG.Monster.Tri.Leech

theorem babyTwoAAutInner
    : BabyTwoAAutInner :=
  babyTwoAAutInner_of CFSG.EvenSmallLie.TwoE6.coverOuterLeTwo Existence.babyTableIII

theorem triangulable_twoAGraph_tGriess
   
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀) :
    Triangulable (twoAGraph Existence.tGriess) := by
  obtain ⟨⟨-, -, -, hcard⟩, -, -, -, -, hA, -⟩ :=
    Existence.monster_existence_clauses_one_two_of_stroth hSLS
  have I : GMSInterfaces (Existence.phiB Existence.uBar) Existence.MGriess :=
    (aSegLiterature_of twoBabyUnique babyTwoAAutInner hSLS).interfaces
      (hSLS _ orderOf_phiB_uBar' Existence.rank_phiB_uBar_sub_one) Existence.MGriess
  have hex := Existence.oddExhaustive_MGriess I
  have hCa := Existence.natCard_cent_tGriess_of (hA _ (IsConj.refl _))
  exact triangulable_twoAGraph_tGriess_of babyTwoAAutInner hSLS
    (Existence.oddTypeOrdersCF_tStarG I hex hcard hCa Existence.exists_hn_two_point')
    (Existence.threeCGenerated_tStarG I hex hcard hCa Existence.exists_hn_two_point')

theorem nonempty_mulEquiv_autO_of_sls
   
    (hSLS : ∀ d₀ : B, orderOf d₀ = 2 → Matrix.rank (d₀.val.val - 1) = 1860 → SLSStatement d₀)
    (d₀ : B) (hd₀ : orderOf d₀ = 2) (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] (a z : G) (hG : GMSF1Type d₀ a z) :
    Nonempty (G ≃* CFSG.Monster.Griess.AutO) :=
  nonempty_mulEquiv_autO_of_three twoBabyUnique babyTwoAAutInner
    (triangulable_twoAGraph_tGriess hSLS) hSLS d₀ hd₀ hrank G a z hG

end CFSG.Monster.GMS
