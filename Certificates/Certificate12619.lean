module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
import Certificates.Kernel.J4Count.FixCE

public section

namespace Certificates

open CertificateChecks

theorem certificate12619 :
    Nat.card ↥(Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set CFSG.Sporadic.J4.J)) ≤ 2661120 :=
  KernelJ4Count.FixCE.card_centralizer_cE_le'

end Certificates
