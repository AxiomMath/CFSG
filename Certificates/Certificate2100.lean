
module

public import Certificates.Certificate2100Base

public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheckBase
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
import Certificates.Kernel.SporSch.HN.Local2100
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.KS.HNArr

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native in
theorem certificate2100 : (labelChecks = true)
    ∧ (localChecksO (hnsData.orbit ()) = true) := by
  refine ⟨KernelSporSch.HNLocal.label_ok, ?_⟩
  rw [localChecksO, hns_n, natTab_alpha, natTab_beta]
  exact KernelSporSch.HNLocal.localChecks_arr

end Certificates
