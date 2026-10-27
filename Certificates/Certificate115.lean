module

public import CFSG.LieType.Steinberg.Minuscule.CertInputs
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

namespace CertificateChecks.Batch115

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

variable {τ : Tag} (D : MinData τ)

end MinData

private theorem e6Data_checkWeights : e6Data.checkWeights = true := by decide +kernel
private theorem e6Data_checkWeylTable : e6Data.checkWeylTable = true := by decide +kernel
private theorem e6Data_checkSimple : e6Data.checkSimple = true := by decide +kernel
private theorem e6Data_checkWeyl : e6Data.checkWeyl = true := by decide +kernel
private theorem e6Data_checkPairs : e6Data.checkPairs = true := by decide +kernel
private theorem e6Data_checkBraid : e6Data.checkBraid = true := by decide +kernel
private theorem e6Data_checkPGen : e6Data.checkPGen = true := by decide +kernel
private theorem e6Data_checkGrading : e6Data.checkGrading = true := by decide +kernel

private theorem e7Data_checkWeights : e7Data.checkWeights = true := by decide +kernel
private theorem e7Data_checkWeylTable : e7Data.checkWeylTable = true := by decide +kernel
private theorem e7Data_checkSimple : e7Data.checkSimple = true := by decide +kernel
private theorem e7Data_checkWeyl : e7Data.checkWeyl = true := by decide +kernel
private theorem e7Data_checkPairs : e7Data.checkPairs = true := by decide +kernel
private theorem e7Data_checkBraid : e7Data.checkBraid = true := by decide +kernel
private theorem e7Data_checkPGen : e7Data.checkPGen = true := by decide +kernel
private theorem e7Data_checkGrading : e7Data.checkGrading = true := by decide +kernel

end CertificateChecks.Batch115

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule in
open CFSG.Blueprint.Chevalley in
theorem certificate115 : (e6Data.checkWeights = true)
    ∧ (e6Data.checkWeylTable = true)
    ∧ (e6Data.checkSimple = true)
    ∧ (e6Data.checkWeyl = true)
    ∧ (e6Data.checkPairs = true)
    ∧ (e6Data.checkBraid = true)
    ∧ (e6Data.checkPGen = true)
    ∧ (e6Data.checkGrading = true)
    ∧ (e7Data.checkWeights = true)
    ∧ (e7Data.checkWeylTable = true)
    ∧ (e7Data.checkSimple = true)
    ∧ (e7Data.checkWeyl = true)
    ∧ (e7Data.checkPairs = true)
    ∧ (e7Data.checkBraid = true)
    ∧ (e7Data.checkPGen = true)
    ∧ (e7Data.checkGrading = true) := by
  exact ⟨CertificateChecks.Batch115.e6Data_checkWeights, CertificateChecks.Batch115.e6Data_checkWeylTable, CertificateChecks.Batch115.e6Data_checkSimple, CertificateChecks.Batch115.e6Data_checkWeyl, CertificateChecks.Batch115.e6Data_checkPairs, CertificateChecks.Batch115.e6Data_checkBraid, CertificateChecks.Batch115.e6Data_checkPGen, CertificateChecks.Batch115.e6Data_checkGrading, CertificateChecks.Batch115.e7Data_checkWeights, CertificateChecks.Batch115.e7Data_checkWeylTable, CertificateChecks.Batch115.e7Data_checkSimple, CertificateChecks.Batch115.e7Data_checkWeyl, CertificateChecks.Batch115.e7Data_checkPairs, CertificateChecks.Batch115.e7Data_checkBraid, CertificateChecks.Batch115.e7Data_checkPGen, CertificateChecks.Batch115.e7Data_checkGrading⟩

end Certificates
