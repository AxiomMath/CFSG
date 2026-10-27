module

public import CFSG.Quasithin.Background.HSporLatM23Sg
import Certificates.Kernel.M23Dc.Facts
import Certificates.Kernel.M23Dc.Sigma

public section

namespace Certificates

open CFSG.KD.M23Dc

open CFSG.Quasithin.H.MathieuLat in
theorem certificate121001 :
    ∀ j ∈ ({4, 6} : Finset ℕ), ∀ k ∈ ({4, 6, 10, 11, 12, 13, 14} : Finset ℕ),
      ∀ e x σ : ↥CFSG.Blueprint.NativeSporadic.M23, e ∈ m23Member j → orderOf e = 3 →
        x ∈ m23Member k → x ∉ m23Member j → orderOf x = 3 → e * x = x * e → σ ∈ m23SylTwo →
        σ * e * σ⁻¹ = e⁻¹ → σ * x * σ⁻¹ = x → False := by
  simp only [← m23K_Y_eq, ← m23K_S_eq]
  exact m23K_sigma_test

end Certificates
