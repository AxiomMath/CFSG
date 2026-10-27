module

public import CFSG.RankThree.Native.ONTripleMatSound
import Certificates.Kernel.Misc.ON.Base
import Certificates.Kernel.Misc.ON.Sig

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON CFSG.RankThree.Native.ONTriple

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple in
theorem certificate8146 :
    (∀ j < 2, ∀ l < 4, eM ((rL.getD j []).getD l 0) =
      (((lineWords.getD j []).getD l []).map fun k => eM (if k = 0 then rN1 else rN2)).prod) ∧
    (∀ j < 2, ∀ m < 3, ∀ i < 3,
      eM (vRegI j m i) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (vRegI j m i)) ∧
    (MapsB (eM rY1) (sYList.getD 0 []) ∧ MapsB (eM rY3) (sYList.getD 1 [])) ∧
    eM rX12 = eM (rX.getD 1 0) * eM (rX.getD 2 0) :=
  ⟨fun _ hj _ hl => chkLM_spec regOKK chkLMB hj hl,
    fun _ hj _ hm _ hi => chkVx0M_spec regOKK chkVx0MB hj hm hi, chkYM_spec regOKK pivK chkYMB,
    chkX12M_spec regOKK chkX12MB⟩

end Certificates
