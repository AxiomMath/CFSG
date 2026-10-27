module

public import CFSG.Quasithin.Recognition.RuTypeSigma
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.Open CFSG.LieType.BorelTits MatrixGroups commutatorElement

namespace CertificateChecks.Batch17033

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.Open CFSG.LieType.BorelTits MatrixGroups commutatorElement

private theorem fix_order_five_0 :  ∀ g : SigmaL2F4, (g ^ 5 = 1 ∧ g ≠ 1) →
    ∀ v : Fin 2 → F4, sigmaAct g v = v → v = 0  := by
  decide +kernel

private theorem card_centralizer_five_1 :  ∀ t : SigmaL2F4, (t ^ 5 = 1 ∧ t ≠ 1) →
    Fintype.card {g : SigmaL2F4 // g * t = t * g} = 5  := by
  decide +kernel

end CertificateChecks.Batch17033

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.Open CFSG.LieType.BorelTits MatrixGroups commutatorElement in
theorem certificate17033 : (
 ∀ g : SigmaL2F4, (g ^ 5 = 1 ∧ g ≠ 1) →
    ∀ v : Fin 2 → F4, sigmaAct g v = v → v = 0 
)
    ∧ (
 ∀ t : SigmaL2F4, (t ^ 5 = 1 ∧ t ≠ 1) →
    Fintype.card {g : SigmaL2F4 // g * t = t * g} = 5 
) := by
  exact ⟨@CertificateChecks.Batch17033.fix_order_five_0, @CertificateChecks.Batch17033.card_centralizer_five_1⟩

end Certificates
