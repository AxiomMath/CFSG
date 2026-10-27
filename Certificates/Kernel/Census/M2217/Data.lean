module

public import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.M2217
  "Certificates/Kernel/Census/M2217/data/m2217.json.gz" 260247 1612780756844970408
  (m2217SG : Array Nat) (m2217Roots : Array Nat) (m2217Nodes : Array NodeP) (m2217CS : ArrCertP)
  (m2217WCS : Array (Array ArrCertP)) (m2217PFS : Array PerfWP) (m2217XG : Array Nat)
  (m2217XS : Array Nat) (m2217XW : List (List Nat))

public section

namespace CertificateChecks.KernelCensus.M2217

open CFSG.KC.Census

@[expose] noncomputable def outXP (P : Nat) : Bool :=
  Nat.beq (at' 5 P 0) 0 && Nat.beq (at' 5 P 1) 1

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK2 24 5 [0, 1, 2, 3, 4, 5, 8, 9] (pinXL m2217XS) outXP true false false m2217CS m2217Nodes
    (pcN 24 5 m2217Nodes) m2217WCS m2217PFS i

@[expose] noncomputable def wordF (k : Nat) : Bool :=
  (m2217XW.getD k []).all (fun i => Nat.blt i m2217XG.size) &&
    Nat.beq m2217XS[k]! (pprod 24 5 ((m2217XW.getD k []).map fun i => m2217XG[i]!))

end CertificateChecks.KernelCensus.M2217

end
