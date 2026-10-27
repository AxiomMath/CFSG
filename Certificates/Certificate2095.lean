module

public import CFSG.Sporadic.HNSchreier.ArchCheckInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
import Certificates.Support.HN2095TreeDecide
meta import Certificates.Support.HN2095TreeDecide
import all Init.Data.String.Defs
import all Init.Data.Nat.Fold
import CFSG.Sporadic.HNSchreier.OrbitCheck
meta import CFSG.Sporadic.HNSchreier.ArchCheckInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option cfsg.hn2095.chunkSize 512
set_option cfsg.hn2095.masked true
set_option cfsg.hn2095.window true

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

namespace CertificateChecks.Batch2095

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

private theorem arch_checks :
    archDataChecks (hexDumpBytes arraysPayload) = true ∧
      archEqChecks (hexDumpBytes arraysPayload) (hnsData.orbit ()) = true := by
  hn_archive_tree_certificate

private theorem arch_data_cert_0 : archDataChecks (hexDumpBytes arraysPayload) = true :=
  arch_checks.1

private theorem arch_eq_cert_1 : archEqChecks (hexDumpBytes arraysPayload) (hnsData.orbit ()) = true :=
  arch_checks.2

end CertificateChecks.Batch2095

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native in
theorem certificate2095 : (archDataChecks (hexDumpBytes arraysPayload) = true)
    ∧ (archEqChecks (hexDumpBytes arraysPayload) (hnsData.orbit ()) = true) := by
  exact ⟨CertificateChecks.Batch2095.arch_data_cert_0, CertificateChecks.Batch2095.arch_eq_cert_1⟩

end Certificates
