module

public import Certificates.Certificate4206

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix
open CFSG.Quasithin.J4Loc (z0)

theorem orbit_cover (_hF : J4Facts) {ℓ : ℕ}
    (hℓ : ℓ = 5 ∨ ℓ = 6) {h : J} (hh : h ∈ Hj) :
    ∃ i < 49, ∃ q ∈ P0, q • (h • (uEl ℓ • w₀)) =
      (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ • w₀ :=
  Certificates.certificate4206.1 ℓ hℓ h hh

theorem exc_cert (_hF : J4Facts) {i : ℕ} (hi : i < 49)
    (hexc : (repData.getD i ⟨0, "", true, 0⟩).exc = true) :
    zEl (repData.getD i ⟨0, "", true, 0⟩) * z0 * (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ ∈
      Eg uJ 11 :=
  Certificates.certificate4206.2 i hi hexc

end CFSG.Quasithin.J4Ov
