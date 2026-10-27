module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.H13.LocDblProfDefs
public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.EaLat318002.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Open CFSG.Quasithin.H13.LocDbl.M24Prof in
theorem certificate318002 : ∀ E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, IsElemAbelian 2 E → 32 ≤ Nat.card E →
    ProfileOK E :=
  KernelEaLat318002.m24_profile_kc

end Certificates
