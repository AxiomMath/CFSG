module

public import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.M22II
  "Certificates/Kernel/Census/M22II/data/m22II.json.gz" 267910 5770048984271264296
  (m22IISG : Array Nat) (m22IIRoots : Array Nat) (m22IINodes : Array NodeP) (m22IICS : ArrCertP)
  (m22IIWCS : Array (Array ArrCertP)) (m22IIXG : Array Nat) (m22IIXS : Array Nat)
  (m22IIXW : List (List Nat))

public section

namespace CertificateChecks.KernelCensus.M22II

open CFSG.KC.Census

@[expose] noncomputable def outXP (P : Nat) : Bool :=
  Nat.beq (at' 5 P 0) 0 && Nat.beq (at' 5 P 1) 1

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK 24 5 [0, 1, 2, 3, 4, 5, 8, 9] (pinXL m22IIXS) outXP false true false m22IICS m22IINodes
    (pcN 24 5 m22IINodes) m22IIWCS i

@[expose] noncomputable def wordF (k : Nat) : Bool :=
  (m22IIXW.getD k []).all (fun i => Nat.blt i m22IIXG.size) &&
    Nat.beq m22IIXS[k]! (pprod 24 5 ((m22IIXW.getD k []).map fun i => m22IIXG[i]!))

end CertificateChecks.KernelCensus.M22II

end
