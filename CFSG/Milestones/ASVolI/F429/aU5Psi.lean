module

public import CFSG.Milestones.ASVolI.F429.aU5Chart
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F429.aU5Chart

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ASVolI.ChF.ClassicalRoots

section U5Marking

variable {f : ℕ} {H : Type} [Group H] (marking : Marking .U5 2 f H)

noncomputable def burnsideF429a_U5_Psi :
    hypPSU (burnsideF429a_U5_fieldData marking) 2 1 ≃* H :=
  (hypPSUEquivStatedProj (burnsideF429a_U5_fieldData marking)
    (burnsideF429a_U5_isHypTransport marking) (by norm_num)).trans marking.identification

theorem burnsideF429a_U5_Psi_hypProj (g : hypSU (burnsideF429a_U5_fieldData marking) 2 1) :
    burnsideF429a_U5_Psi marking (hypProj (burnsideF429a_U5_fieldData marking) 2 1 g) =
      marking.transport (burnsideF429a_U5_T marking g) := by
  show marking.identification (hypPSUEquivStatedProj (burnsideF429a_U5_fieldData marking)
    (burnsideF429a_U5_isHypTransport marking) (by norm_num)
      (hypProj (burnsideF429a_U5_fieldData marking) 2 1 g)) = _
  rw [hypPSUEquivStatedProj_hypProj]
  rfl

theorem burnsideF429a_U5_Psi_comp :
    (burnsideF429a_U5_Psi marking).toMonoidHom.comp
        (hypProj (burnsideF429a_U5_fieldData marking) 2 1) =
      marking.transport.comp (burnsideF429a_U5_T marking).toMonoidHom :=
  MonoidHom.ext fun g => burnsideF429a_U5_Psi_hypProj marking g

theorem burnsideF429a_U5_Psi_parabolic :
    marking.parabolic false =
        (H13.Sec53F.Unit.u5PtP (burnsideF429a_U5_fieldData marking)).map
          (burnsideF429a_U5_Psi marking).toMonoidHom ∧
      marking.parabolic true =
        (H13.Sec53F.Unit.u5LnP (burnsideF429a_U5_fieldData marking)).map
          (burnsideF429a_U5_Psi marking).toMonoidHom := by
  refine ⟨?_, ?_⟩
  · rw [H13.Sec53F.Unit.u5PtP, projIsoStabilizer, Subgroup.map_map, burnsideF429a_U5_Psi_comp,
      ← Subgroup.map_map, ← burnsideF429a_U5_parabolic_false]
    rfl
  · rw [H13.Sec53F.Unit.u5LnP, projIsoStabilizer, Subgroup.map_map, burnsideF429a_U5_Psi_comp,
      ← Subgroup.map_map, ← burnsideF429a_U5_parabolic_true]
    rfl

end U5Marking

section Chart

variable {f : ℕ} {E : Type} [Group E]

theorem burnsideF429a_U5_payload_eq {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .U5 2 f Gp M₁ M₂) :
    ∃ mk : Marking .U5 2 f ↥Gp,
      hyp.chart.coordinatePayload = NativeCoordinates.classical .U5 rfl mk ∧
      Gp ⊓ M₁ = (mk.parabolic false).map Gp.subtype ∧
      Gp ⊓ M₂ = (mk.parabolic true).map Gp.subtype := by
  have hfits := hyp.chart.coordinatePayload_fits
  have hm := hyp.chart_matches
  generalize hcp : hyp.chart.coordinatePayload = cp at hfits
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .U5 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    refine ⟨mk, rfl, ?_, ?_⟩
    · rw [hm.2.1]
      exact hpts
    · rw [hm.2.2]
      exact hlns
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

theorem burnsideF429a_U5_subgroupOf_eq {Gp M : Subgroup E} (mk : Marking .U5 2 f ↥Gp) {b : Bool}
    (hM : Gp ⊓ M = (mk.parabolic b).map Gp.subtype) :
    M.subgroupOf Gp = (if b then H13.Sec53F.Unit.u5LnP (burnsideF429a_U5_fieldData mk)
      else H13.Sec53F.Unit.u5PtP (burnsideF429a_U5_fieldData mk)).map
        (burnsideF429a_U5_Psi mk).toMonoidHom := by
  have e : M.subgroupOf Gp = mk.parabolic b := by
    rw [← Subgroup.inf_subgroupOf_left M Gp, hM]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  rw [e]
  cases b
  · exact (burnsideF429a_U5_Psi_parabolic mk).1
  · exact (burnsideF429a_U5_Psi_parabolic mk).2

end Chart

end CFSG.ASVolI
