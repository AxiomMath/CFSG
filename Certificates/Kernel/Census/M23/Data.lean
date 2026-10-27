module

public import Certificates.Kernel.Census.M23.Chain
public import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.M23K
  "Certificates/Kernel/Census/M23/data/m23.json.gz" 56731 17167413984340180680
  (m23SG : Array Nat) (m23Roots : Array Nat) (m23Nodes : Array NodeP) (m23CS : ArrCertP)
  (m23WCS : Array (Array ArrCertP)) (m23PFS : Array PerfWP)

public section

namespace CertificateChecks.KernelCensus.M23K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 23 5 (mask 5) (23 * 5) (pidn 23 5) M23C.LR M23C.TRI M23C.BP 6 0 P

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK2 23 5 [0, 1, 2, 3, 4, 5, 6] inP (fun _ => true) true false false m23CS m23Nodes
    (pcN 23 5 m23Nodes) m23WCS m23PFS i

end CertificateChecks.KernelCensus.M23K

end
