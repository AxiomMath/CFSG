module

public import Certificates.Data.Kernel.J2Cent
public import Certificates.Kernel.C12643.Elts
public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelC12643 "Certificates/Kernel/C12643/data/c12643cent.json.gz" 1937 6217788828403252904
  (CT5 : List Nat) (CT7 : List Nat)

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Cent CertificateChecks.KernelJ2Cover

@[expose] noncomputable def fC5 (a : Nat) : Bool :=
  Nat.beq (blkCent 315 9 PA.LR PA.TR PA.BP X5A X5C a) (lget CT5 (blkKey 315 9 PA.LR PA.TR PA.BP a))

@[expose] noncomputable def fC7 (a : Nat) : Bool :=
  Nat.beq (blkCent 315 9 PA.LR PA.TR PA.BP X7 E1 a) (lget CT7 (blkKey 315 9 PA.LR PA.TR PA.BP a))

end CertificateChecks.KernelC12643

end
