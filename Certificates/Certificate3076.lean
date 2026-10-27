
module

public import Certificates.Certificate3076Base

public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import CFSG.Certificates.Kernel.SortTreeSound
public import Certificates.Kernel.MonsterB.Sp8OrbData
public import Mathlib.Data.Nat.Bits
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.KC.SortTree
  CFSG.KLie.CT

namespace CertificateChecks.Batch3076

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.KC.SortTree
  CFSG.KLie.CT

set_option maxRecDepth 100000

end CertificateChecks.Batch3076

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.Monster.B.TwoA.Census in
theorem certificate3076 : (∀ v : V8, ∃ x < 256, bvec 8 x = v)
    ∧ (natCertOK vecAct 45 vecValid 1 vecCert = true ∧ vecCert.pts.size = 255 ∧
       ∀ x < 256, x ≠ 0 → ∃ i < 255, vecCert.pts[i]! = x)
    ∧ (natCertOK tupAct 23 tupValid tupRoot tupCert = true ∧
       tupCert.pts.size = 128) :=
  ⟨CertificateChecks.Batch3076.exists_bvec 8, CertificateChecks.Batch3076.vec_ok, CertificateChecks.Batch3076.tup_ok⟩

end Certificates
