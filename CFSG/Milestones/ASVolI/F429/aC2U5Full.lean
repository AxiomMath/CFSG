module

public import CFSG.Milestones.ASVolI.F429.aC2U5Of
public import CFSG.Milestones.ASVolI.F429.bC2cU5Sp

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429a_c2c_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t ∨
        (hyp.toHypF_4_4g.chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f ∧
          hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal t) ∨
        (hyp.toHypF_4_4g.chart.IsTypeIIIInv t ∧ ∃ s z : E,
          t = s * z ∧ hyp.toHypF_4_4g.chart.IsGraphInv s ∧
            hyp.toHypF_4_4g.chart.coordinatePayload.RankInvolution 1 z ∧ s * z = z * s ∧
            IsGenLie ↥(cenIn Gp s) .Sp4 2 f ∧ hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal s ∧
            Subgroup.centralizer ({t} : Set E) =
              Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E)) :=
  burnsideF429a_c2c_U5_of hyp hT
    (fun mk _ y _ ht => burnsideF429b_U5_isGenLie_act _ (burnsideF429a_U5_Psi mk) y ht)
    (fun mk hcp _ _ hy ht => burnsideF429b_U5_graphFixed_act _ hyp.toHypF_4_4g.chart
      (burnsideF429a_U5_Psi mk) hy ht
      (fun w hw => burnsideF429a_U5_rankInv_iff hyp.toHypF_4_4g.chart hcp w hw))

end CFSG.ASVolI
