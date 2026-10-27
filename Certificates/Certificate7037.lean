
module

public import CFSG.Quasithin.Recognition.L34AmalgamGenInputs
public import CFSG.Quasithin.Recognition.L34AmalgamDataBase
import CFSG.Sporadic.Schreier.M22Data
meta import CFSG.Sporadic.Schreier.M22Data
import Certificates.Kernel.LocalComp.WittA7035

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 in
theorem certificate7037 :
    (∀ s ∈ bWords, ∀ x ∈ word s, x.1.val < 3)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
       ¬ ∃ T ∈ bTabs, ∀ x : Fin 22, σ x = T.getD x.val 0) = 0) :=
  ⟨KernelLC.Witt.bWords_letters, KernelLC.Witt.count_B⟩

end Certificates
