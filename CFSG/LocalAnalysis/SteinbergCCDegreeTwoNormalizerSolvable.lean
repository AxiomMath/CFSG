module

public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection

public section

namespace CFSG.LocalAnalysis

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

theorem eq_smul_one_add_smul_of_commute {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 2) {t : V →ₗ[k] V} {v : V} (hv : LinearIndependent k ![v, t v])
    {B : V →ₗ[k] V} (hB : B * t = t * B) : ∃ a c : k, B = a • 1 + c • t := by
  let bas := basisOfLinearIndependentOfCardEqFinrank hv (by rw [Fintype.card_fin, hV])
  have hbas : ∀ i, bas i = ![v, t v] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  obtain ⟨a, c, hBv⟩ : ∃ a c : k, B v = a • v + c • t v := by
    refine ⟨bas.repr (B v) 0, bas.repr (B v) 1, ?_⟩
    conv_lhs => rw [← bas.sum_repr (B v)]
    rw [Fin.sum_univ_two, hbas, hbas]
    rfl
  refine ⟨a, c, bas.ext fun i => ?_⟩
  fin_cases i
  · rw [hbas]
    simpa using hBv
  · rw [hbas]
    have h1 : B (t v) = t (B v) := by
      have := congrArg (fun f : V →ₗ[k] V => f v) hB
      simpa using this
    show B (t v) = (a • (1 : V →ₗ[k] V) + c • t) (t v)
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, h1,
      hBv, map_add, map_smul, map_smul]

end CFSG.LocalAnalysis
