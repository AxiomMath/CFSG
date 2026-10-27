module

public import Certificates.Data.CFSGNative.SporLat.Spec
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import Certificates.Certificate121001
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.Stellmacher.L3YC

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.E2P.SporB

section M23

theorem m23_sigma_test :
    ∀ j ∈ ({4, 6} : Finset ℕ), ∀ k ∈ ({4, 6, 10, 11, 12, 13, 14} : Finset ℕ),
      ∀ e x σ : ↥CFSG.Blueprint.NativeSporadic.M23, e ∈ m23CtxB.Y j → orderOf e = 3 →
        x ∈ m23CtxB.Y k → x ∉ m23CtxB.Y j → orderOf x = 3 → e * x = x * e → σ ∈ m23CtxB.S →
        σ * e * σ⁻¹ = e⁻¹ → σ * x * σ⁻¹ = x → False := by
  rw [m23Ctx_S]
  simp only [m23Ctx_Y]
  exact Certificates.certificate121001

end M23

end CFSG.Quasithin.Stellmacher.L3YC
