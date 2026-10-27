module

public import CFSG.LocalAnalysis.StandardType.PhanEStdE8
public import CFSG.LocalAnalysis.StandardType.PhanEAdjDescent
public import CFSG.LocalAnalysis.StandardType.PhanEFrobDescent

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

variable {k : Type} [Field k] [Finite k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e8FrobFixEquiv {k₀ : Type} [Field k₀]
    (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) (ι : k₀ →+* k)
    (hι : ∀ c, θ (ι c) = ι c) (hdesc : ∀ c, θ c = c → ∃ c', ι c' = c) :
    ↥(adjointGroup .E8 k₀) ≃* frobFix (e8Frob θ hθ) :=
  frobFixEquivOfDescent (e8_isCTGroupDatum k) (e8Frob θ hθ) (e8_steinbergExtras k)
    (e8W0_isLongest k) (e8_bruhatExtras k) (e8StdLevi θ hθ hnorm) (fun _ => rfl) rfl
    (fun γ hγ => by
      rintro _ ⟨x, hx, rfl⟩
      exact (adj_isTwist (τ := .E8) θ hθ).map_rootGroup γ hγ x hx)
    (adjointBaseChangeHom .E8 ι) (adjointBaseChangeHom_injective .E8 ι)
    (adjBC_fixed (τ := .E8) θ hθ ι hι)
    (fun γ hγ x hx hfix => adjBC_descent_rootGroup (τ := .E8) θ hθ ι hdesc
      ((mem_adjDatum_roots).1 hγ) hx hfix)

end CFSG.ClassicalInvolution.Phan.PhanE
