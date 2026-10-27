module

public import Certificates.Data.Kernel.Co2CenLook
public import Certificates.Kernel.Co2JRank.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.GL "Certificates/Kernel/Co2Cen/data/gl.items" 1049 6809562163057471056

namespace CertificateChecks.KernelSpor.Co2Cen

@[expose] noncomputable def WW1 (k : Nat) : Nat := GL k
@[expose] noncomputable def WL1 (k : Nat) : Nat := GL (Nat.add (nat_lit 5) k)
@[expose] noncomputable def LW (s : Nat) : Nat := GL (Nat.add (nat_lit 10) s)
@[expose] noncomputable def LZ (m : Nat) : Nat := GL (Nat.add (nat_lit 25) m)
@[expose] noncomputable def RK (j : Nat) : Nat := GL (Nat.add (nat_lit 40) j)

@[expose] noncomputable def lwU (s : Nat) : Nat := Nat.land (LW s) (nat_lit 31)
@[expose] noncomputable def lwA (s : Nat) : Nat :=
  Nat.land (Nat.shiftRight (LW s) (nat_lit 5)) (nat_lit 16777215)
@[expose] noncomputable def lwB (s : Nat) : Nat := Nat.shiftRight (LW s) (nat_lit 29)

@[expose] noncomputable def WGx (i : Nat) : Nat :=
  CFSG.KC.Co2InvS.selN (Nat.blt i (nat_lit 5)) (Co2JRank.WG i) CFSG.KC.Co2InvS.IDP

@[expose] def x3W : List Nat := [26, 4, 6, 7, 5]
@[expose] def x7W : List Nat := [26, 28, 29, 6, 14, 17, 20, 8, 7, 5]

end CertificateChecks.KernelSpor.Co2Cen

end
