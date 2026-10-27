module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
import Certificates.Kernel.KDenseP.E11_16953

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Visible CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 in
theorem certificate16953 : Nat.card ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer ({gw gen11W0} : Set Gmat)) ≤ 32 :=
  KernelKDenseP.E11.c16953

end Certificates
