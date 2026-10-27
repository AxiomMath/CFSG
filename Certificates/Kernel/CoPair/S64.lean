module

public import Certificates.Kernel.CoPair.Gens
public import Certificates.Kernel.CoPair.S64Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair

set_option Elab.async false

noncomputable abbrev s64Pt : Nat → Bool := orbPt TX TY S64.P S64.E 46575 10

@[expose] noncomputable def s64F (k : Nat) : Bool :=
  allR (1000 * k) (Nat.min 1000 (46575 - 1000 * k)) s64Pt

#kc_each_unfold s64F 0 47 as CertificateChecks.KernelCoPair.s64c

theorem s64seed : Nat.beq (f24 S64.P 10) 64 = true := by quickRfl

end CertificateChecks.KernelCoPair

end
