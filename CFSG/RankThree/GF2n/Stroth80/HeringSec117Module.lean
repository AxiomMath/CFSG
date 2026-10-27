module

import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

omit [CharP K 2] in
theorem Ctx.mem_Q_of_cmCommAct_eq_one (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e)
    {s : ↥(XbarH M Q Z B)} (hs : cmCommAct hc φ s = 1) :
    ((s : ↥(H0 M Z)) : G) ∈ Q := by
  have hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f := by
    intro g e f
    have h1 := M₀.Qf_add (φ g e) (φ g f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφQ g, hφQ g e, hφQ g f] at h1
    linear_combination h2 - h1
  refine (hφk _).mp (LinearEquiv.ext fun e => ?_)
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    ((hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top ▸ Submodule.mem_top (x := e))
  have hu' : φ (s : ↥(H0 M Z)) u = u := by
    have := congrArg (fun f : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ) =>
      ((f ⟨u, hu⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E)) hs
    simpa [coe_cmCommAct] using this
  rw [map_add, hu', hc.fix_of_mem_orthogonal_cmComm hD φ hφπ hφB s hw]
  rfl

end CFSG.RankThree.GF2n.Stroth80
