module

public import CFSG.Milestones.ASVolI.F429.aC2cU4
public import CFSG.Milestones.ASVolI.F429.U4Graph
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.U4Par
  CFSG.ClassicalGroups.UnitaryFlag

theorem burnsideF429a_c2c_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
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
  obtain ⟨mk, hcp, h1, h2⟩ := burnsideF429a_U4_payload_eq hyp.toHypF_4_4g
  have hP₁ : M₁.subgroupOf Gp = (parP (burnsideF4gU4_fieldData mk)).map
      (burnsideF4gU4_Phi mk).toMonoidHom := burnsideF429a_U4_subgroupOf_eq mk h1
  have hP₂ : M₂.subgroupOf Gp = (parP2 (burnsideF4gU4_fieldData mk)).map
      (burnsideF4gU4_Phi mk).toMonoidHom := burnsideF429a_U4_subgroupOf_eq mk h2
  have hSG := burnsideF429a_U4_sylow_of_model _ (burnsideF4gU4_Phi mk) hP₁ hP₂
  obtain ⟨-, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  have htG : t ∉ Gp := fun htG => htS (by rw [← hTinf]; exact ⟨htT, htG⟩)
  have hgraph : ∀ (s : E) (a : hypSU (burnsideF4gU4_fieldData mk) 2 0),
      (∀ x, ((burnsideF4gU4_Phi mk (a * frobElt (burnsideF4gU4_fieldData mk) x * a⁻¹) :
        ↥Gp) : E) = s * ((burnsideF4gU4_Phi mk (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹) →
      hyp.toHypF_4_4g.chart.IsGraphInv s ∧ IsGenLie ↥(cenIn Gp s) GLKind.Sp4 2 f ∧
        hyp.toHypF_4_4g.chart.GraphFixedMarkingGoal s := by
    intro s a hs
    obtain ⟨hsG, hs2⟩ := burnsideF429a_U4_graph_inv _ hyp.centralizer_trivial
      (burnsideF4gU4_Phi mk) a hs
    refine ⟨?_, burnsideF429_U4_isGenLie _ (burnsideF4gU4_Phi mk) a hs,
      burnsideF429_U4_graphFixed hyp.toHypF_4_4g.chart mk hcp a hs⟩
    have key : hyp.toHypF_4_4g.chart.IsGraphInv s ↔
        s ∉ Gp ∧ s * s = 1 ∧ 0 < f ∧ hyp.toHypF_4_4g.chart.coordinatePayload.GraphAction s :=
      Iff.rfl
    rw [key, hcp]
    exact ⟨hsG, hs2, mk.exponent_pos, burnsideF429a_U4_graphAction mk a hs⟩
  obtain ⟨a, ha | ha⟩ := burnsideF429a_U4_inv_classify _ hyp.centralizer_trivial
    (burnsideF4gU4_Phi mk) hP₁ hP₂ (hT.1 htT) htG ht2
  · exact Or.inr (Or.inl (hgraph t a ha))
  · refine Or.inr (Or.inr ?_)
    obtain ⟨z, hz⟩ : ∃ z : E, z = ((burnsideF4gU4_Phi mk
        (a * burnsideF429a_U4_z0 (burnsideF4gU4_fieldData mk) * a⁻¹) : ↥Gp) : E) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : E, s = t * z⁻¹ := ⟨_, rfl⟩
    obtain ⟨hsact, hsz⟩ := burnsideF429a_U4_typeIII_split _ hyp.centralizer_trivial
      (burnsideF4gU4_Phi mk) a ha hz hs
    have hts : t = s * z := by rw [hs]; group
    obtain ⟨hsG, hsGL, hsM⟩ := hgraph s a hsact
    have hzR : hyp.toHypF_4_4g.chart.coordinatePayload.RankInvolution 1 z := by
      rw [hz]
      exact burnsideF429a_U4_rankInv_z0 hyp.toHypF_4_4g hcp a
    refine ⟨⟨rfl, s, z, hts, hsG, hzR, hsz⟩, s, z, hts, hsG, hzR, hsz, hsGL, hsM, ?_⟩
    exact burnsideF429a_U4_centralizer_typeIII _ hyp.centralizer_trivial hyp.split
      (burnsideF4gU4_Phi mk) hP₁ hP₂ a ha hz hts

end CFSG.ASVolI
