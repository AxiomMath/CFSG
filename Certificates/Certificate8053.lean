module

public import CFSG.Timmesfeld.Exceptional.DeepAllNearInputs
import Certificates.Kernel.Misc.Coset.C8053

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Timmesfeld.Moufang.Deep CFSG.Certificates
  CFSG.CosetTable in
theorem certificate8053 : (Finite (PG 7 (relsAN ++ [prodAN])) ∧ Nat.card (PG 7 (relsAN ++ [prodAN])) ≤ 1) ∧
    (Finite (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ∧
      Nat.card (PG 7 (relsAN ++ [prodAN ++ [letAN 0 false]])) ≤ 1) := KernelMiscCoset.C8053.card_le

end Certificates
