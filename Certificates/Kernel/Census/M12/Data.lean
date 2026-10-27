module

public import Certificates.Kernel.Census.M12Chain
public import Certificates.Data.Kernel.Census.PackedExc
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.M12K
  "Certificates/Kernel/Census/M12/data/m12.json.gz" 50986 10525387374304758693
  (m12SG : Array Nat) (m12Roots : Array Nat) (m12Nodes : Array NodeP) (m12CS : ArrCertP)
  (m12WCS : Array (Array ArrCertP)) (m12Excs : List ExcRefP) (m12E0P : Array Nat)

public section

namespace CertificateChecks.KernelCensus.M12K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M12C.LR M12C.TRI M12C.BP 5 0 P

@[expose] def sigP : Nat := 0x5a928398a418820bdab49ca307b9ac

@[expose] noncomputable def inRP (P : Nat) : Bool := inP P || inP (pc 24 5 sigP P)

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeExcOK 24 5 [0, 1, 2, 3, 4, 12, 13, 14, 15, 16] inP inP inRP false false false m12CS m12Nodes
    (pcN 24 5 m12Nodes) m12WCS m12E0P m12Excs i

end CertificateChecks.KernelCensus.M12K

end
