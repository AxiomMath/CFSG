module

public import Certificates.Data.Kernel.Co2CenTree
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.I1 "Certificates/Kernel/Co2Cen/data/i1.items" 5118 6561806353463287997
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.I8 "Certificates/Kernel/Co2Cen/data/i8.items" 638 124945209181586574

namespace CertificateChecks.KernelSpor.Co2Cen

@[expose] noncomputable def PE1 (s : Nat) : Nat := I1 s
@[expose] noncomputable def PM1 (s : Nat) : Nat := I1 (Nat.add (nat_lit 128) s)
@[expose] noncomputable def PS1 (s : Nat) : Nat := I1 (Nat.add (nat_lit 256) s)
@[expose] noncomputable def PT1 (s j : Nat) : Nat :=
  fld(I1 (Nat.add (nat_lit 384) s), Nat.mul (nat_lit 16) j, nat_lit 65535)

@[expose] noncomputable def PE8 (s : Nat) : Nat := I8 s
@[expose] noncomputable def PM8 (s : Nat) : Nat := I8 (Nat.add (nat_lit 16) s)
@[expose] noncomputable def PS8 (s : Nat) : Nat := I8 (Nat.add (nat_lit 32) s)
@[expose] noncomputable def PT8 (s j : Nat) : Nat :=
  fld(I8 (Nat.add (nat_lit 48) s), Nat.mul (nat_lit 16) j, nat_lit 65535)

end CertificateChecks.KernelSpor.Co2Cen

end
