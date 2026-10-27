module

public import CFSG.Sporadic.HNSchreier.VectorData
public import CFSG.Sporadic.HNSchreier.LevelInputs
import Certificates.Kernel.HNChain.FormFacts
import Certificates.Kernel.HNChain.Level
import Certificates.Kernel.HNChain.Neg
import Certificates.Kernel.HN3166.Card
import Certificates.Certificate9114
import Certificates.Certificate9208

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native Matrix in
theorem certificate2107 : (formMᵀ = formM ∧ formM.det ≠ 0 ∧ matAᵀ * formM * matA = formM ∧
      matBᵀ * formM * matB = formM)
    ∧ (Nat.card (J hnsData) = 273030912000000 ∧ LevelFacts) :=
  ⟨KernelHNChain.Form.form_parts, KernelHN.card_J, KernelHNChain.levelFacts⟩

end Certificates
