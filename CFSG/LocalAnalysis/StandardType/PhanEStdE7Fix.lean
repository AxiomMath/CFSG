module

public import CFSG.LocalAnalysis.StandardType.PhanEStdE7
public import CFSG.LocalAnalysis.StandardType.PhanEMinDescent
public import CFSG.LocalAnalysis.StandardType.PhanEFrobDescent
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {k : Type} [Field k] [Finite k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e7FrobFixEquiv {k₀ : Type} [Field k₀]
    (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) (ι : k₀ →+* k)
    (hι : ∀ c, θ (ι c) = ι c) (hdesc : ∀ c, θ c = c → ∃ c', ι c' = c) :
    e7Data_valid.minGroup k₀ ≃* frobFix (e7Frob θ hθ) :=
  frobFixEquivOfDescent (e7Datum_isCTGroupDatum k) (e7Frob θ hθ) (e7Datum_steinbergExtras k)
    (e7W0_isLongest k) (e7Datum_bruhatExtras k) (e7StdLevi θ hθ hnorm) (fun _ => rfl) rfl
    (fun γ _ => map_rootGroup_minBC_le e7Data_valid θ γ) (minBC e7Data_valid ι)
    (minBC_injective' e7Data_valid ι) (minBC_fixed e7Data_valid θ ι hι)
    (fun γ hγ x hx hfix => minBC_descent_rootGroup e7Data_valid θ ι hdesc
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 k).1 hγ) hx hfix)

end CFSG.ClassicalInvolution.Phan.PhanE
