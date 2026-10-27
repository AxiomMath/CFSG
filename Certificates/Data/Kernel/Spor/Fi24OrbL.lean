module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.Spor.Fi24Orb
public import Certificates.Data.CFSGNative.Fi24.Enum

#kc_repo #kc_ktree_gz CFSG.Sporadic.Fi24.OrbL OT "Certificates/Kernel/Sporadic/Fi24Orb/data/orbl.bin.gz" 4096 4 2455488 3999311635137771502

public section

namespace CFSG.Sporadic.Fi24

open CFSG.KC.Fi24Orb

@[expose] noncomputable def OrbL.OLe (k : Nat) : Nat :=
  fld(OrbL.OT (Nat.shiftRight k (nat_lit 9)), Nat.mul (Nat.land k (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def OrbL.tab (f : Nat → Nat) : CFSG.Sporadic.Th.Native.Table :=
  Array.ofFn (n := 306936) fun k => UInt32.ofNat (f (OrbL.OLe k.val))

@[expose] noncomputable def orb : Native.Enum where
  alpha := OrbL.tab oA
  beta := OrbL.tab oB
  par := OrbL.tab oPar
  lab := OrbL.tab oLab
  starts := #[]

end CFSG.Sporadic.Fi24
