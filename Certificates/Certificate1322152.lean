module

public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3109
import Certificates.Kernel.BabyMonster.B31Facts
public import Certificates.Certificate3109Base

public section

namespace Certificates

open CertificateChecks

theorem certificate1322152 : ∃ a c : CFSG.Blueprint.NativeSporadic.B,
    a ^ 31 = 1 ∧ a ≠ 1 ∧ c * a = a ^ 2 * c :=
  ⟨_, _, KernelBM.B31.bThirtyOne_facts⟩

end Certificates
