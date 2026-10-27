module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
import Certificates.Kernel.KDenseP.M13_16957

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Visible CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 in
theorem certificate16957 : Nat.card ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer ({gw genD13W1} : Set Gmat)) ≤ 2 :=
  KernelKDenseP.M13.E16957.c16957

end Certificates
