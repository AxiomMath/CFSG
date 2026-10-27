module

public import CFSG.Milestones.ASVolI.F429.aC2cU5
public import CFSG.Milestones.ASVolI.F429.aC2U5
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429a_c2c_U5_of {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂))
    (hB : ∀ (mk : Marking .U5 2 f ↥Gp) (t : E) (y : Gam (burnsideF429a_U5_fieldData mk)),
      y.1.right = 1 →
      (∀ g : hypSU (burnsideF429a_U5_fieldData mk) 2 1,
        ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y (act _ (fieldElt _
          (barEquiv (burnsideF429a_U5_fieldData mk))) g))) : ↥Gp) : E) =
          t * ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y g)) : ↥Gp) : E) * t⁻¹) →
      IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f)
    (hC : ∀ (mk : Marking .U5 2 f ↥Gp),
      hyp.toHypF_4_4g.chart.coordinatePayload = NativeCoordinates.classical .U5 rfl mk →
      ∀ (t : E) (y : Gam (burnsideF429a_U5_fieldData mk)), y.1.right = 1 →
      (∀ g : hypSU (burnsideF429a_U5_fieldData mk) 2 1,
        ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y (act _ (fieldElt _
          (barEquiv (burnsideF429a_U5_fieldData mk))) g))) : ↥Gp) : E) =
          t * ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y g)) : ↥Gp) : E) * t⁻¹) →
      hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal t) :
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t ∨
        (hyp.toHypF_4_4g.chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f ∧
          hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal t) ∨
        (hyp.toHypF_4_4g.chart.IsTypeIIIInv t ∧ ∃ s z : E,
          t = s * z ∧ hyp.toHypF_4_4g.chart.IsGraphInv s ∧
            hyp.toHypF_4_4g.chart.coordinatePayload.RankInvolution 1 z ∧ s * z = z * s ∧
            IsGenLie ↥(cenIn Gp s) .Sp4 2 f ∧ hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal s ∧
            Subgroup.centralizer ({t} : Set E) =
              Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  intro t htT htS ht2
  obtain ⟨mk, hcp, h1, h2⟩ := burnsideF429a_U5_payload_eq hyp.toHypF_4_4g
  have hP₁ : M₁.subgroupOf Gp = (u5PtP (burnsideF429a_U5_fieldData mk)).map
      (burnsideF429a_U5_Psi mk).toMonoidHom := burnsideF429a_U5_subgroupOf_eq mk h1
  have hP₂ : M₂.subgroupOf Gp = (u5LnP (burnsideF429a_U5_fieldData mk)).map
      (burnsideF429a_U5_Psi mk).toMonoidHom := burnsideF429a_U5_subgroupOf_eq mk h2
  have hBor : (M₁ ⊓ M₂).subgroupOf Gp =
      (u5PtP (burnsideF429a_U5_fieldData mk) ⊓ u5LnP (burnsideF429a_U5_fieldData mk)).map
        (burnsideF429a_U5_Psi mk).toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂,
      Subgroup.map_inf_eq _ _ _ (burnsideF429a_U5_Psi mk).injective]
  have hSG := burnsideF429a_U5_sylow_of_setup _ (burnsideF429a_U5_Psi mk) hBor
  obtain ⟨-, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  have htG : t ∉ Gp := fun htG => htS (by rw [← hTinf]; exact ⟨htT, htG⟩)
  obtain ⟨y, hy, ht⟩ := burnsideF429a_U5_inv_classify _ hyp.centralizer_trivial
    (burnsideF429a_U5_Psi mk) htG ht2
  refine Or.inr (Or.inl ⟨?_, hB mk t y hy ht, hC mk hcp t y hy ht⟩)
  have key : hyp.toHypF_4_4g.chart.IsGraphInv t ↔
      t ∉ Gp ∧ t * t = 1 ∧ 0 < f ∧ hyp.toHypF_4_4g.chart.coordinatePayload.GraphAction t :=
    Iff.rfl
  rw [key, hcp]
  exact ⟨htG, ht2, mk.exponent_pos, burnsideF429a_U5_graphAction mk y hy ht⟩

end CFSG.ASVolI
