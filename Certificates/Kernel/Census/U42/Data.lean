module

public import Certificates.Kernel.Census.U42.Chain
public import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.U42K
  "Certificates/Kernel/Census/U42/data/u42.json.gz" 107183 9653902403226658051
  (u42SG : Array Nat) (u42Roots : Array Nat) (u42Nodes : Array NodeP) (u42CS : ArrCertP)
  (u42WCS : Array (Array ArrCertP))

public section

namespace CertificateChecks.KernelCensus.U42K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 45 6 (mask 6) (45 * 6) (pidn 45 6) U42C.LR U42C.TRI U42C.BP 4 0 P

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK 45 6 [0, 1, 16, 3, 2, 4, 5, 6, 7] inP inP false true false u42CS u42Nodes
    (pcN 45 6 u42Nodes) u42WCS i

end CertificateChecks.KernelCensus.U42K

end
