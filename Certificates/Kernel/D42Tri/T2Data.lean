module

public import Certificates.Data.D42Triality
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.D42Triality
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz_eval CertificateChecks.KernelD42Tri.TD
  "Certificates/Kernel/D42Tri/data/t2.json.gz" 2775 6207383598988234263
  (w1 : List Nat) (w2 : List Nat) (w3 : List Nat) (w4 : List Nat) (w5 : List Nat)
  (w6 : List Nat) (o0p : List Nat) (o0q : List Nat) (o0l : List Nat) (o1p : List Nat)
  (o1q : List Nat) (o1l : List Nat) (o2p : List Nat) (o2q : List Nat) (o2l : List Nat)

#ks_chars CertificateChecks.KernelD42Tri.T2H CFSG.HardMathSupport.Dickson.Bal207.D42TriData.repHex

#kmisc_hexflat CertificateChecks.KernelD42Tri.T2H
  CFSG.HardMathSupport.Dickson.Bal207.D42TriData.repHex 3 360 9 1

end
