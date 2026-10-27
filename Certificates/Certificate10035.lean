module

public import CFSG.Monster.GMS.Griess13.Data
meta import CFSG.Monster.GMS.Griess13.Data
meta import Mathlib
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
meta import CFSG.Sporadic.Co1Base
meta import CFSG.Sporadic.Th.F2Spec

public section

open CFSG.Monster.GMS.Griess13.Co1Data

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.Batch10035

open CFSG.Monster.GMS.Griess13.Co1Data

private theorem repw_injective :
    Function.Injective repw := by
  decide +kernel

private theorem repw_lineRep :
    ∀ k : Fin 12, ∃ i : Fin 6, repw k i = 1 ∧ ∀ j : Fin 6, j < i → repw k j = 0 := by
  decide +kernel

private theorem decSigma_const :
    ∀ (s : Fin 2) (k : Fin 12) (j : Fin 2),
      decSigma s k j = decSigma s k 0 := by
  decide +kernel

end CertificateChecks.Batch10035

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.Griess13.Co1Data in
theorem certificate10035 :
    (Function.Injective repw)
    ∧ (∀ k : Fin 12, ∃ i : Fin 6, repw k i = 1 ∧ ∀ j : Fin 6, j < i → repw k j = 0)
    ∧ (∀ (s : Fin 2) (k : Fin 12) (j : Fin 2),
      decSigma s k j = decSigma s k 0) :=
  ⟨CertificateChecks.Batch10035.repw_injective, CertificateChecks.Batch10035.repw_lineRep, CertificateChecks.Batch10035.decSigma_const⟩

end Certificates
