module

public import CFSG.Quasithin.Background.JonesParshallG2TwoInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open commutatorElement

namespace CertificateChecks.Batch17028

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open commutatorElement

private theorem cmat_g2X_e0_0 : cmat (g2X (![1, 0, 0] : Fin 3 → ZMod 2)) = matX2 := by
  decide +kernel

private theorem cmat_g2Y_e1_1 : cmat (g2Y (![0, 1, 0] : Fin 3 → ZMod 2)) = matY2 := by
  decide +kernel

end CertificateChecks.Batch17028

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open commutatorElement in
theorem certificate17028 : (
 cmat (g2X (![1, 0, 0] : Fin 3 → ZMod 2)) = matX2 
)
    ∧ (
 cmat (g2Y (![0, 1, 0] : Fin 3 → ZMod 2)) = matY2 
) := by
  exact ⟨@CertificateChecks.Batch17028.cmat_g2X_e0_0, @CertificateChecks.Batch17028.cmat_g2Y_e1_1⟩

end Certificates
