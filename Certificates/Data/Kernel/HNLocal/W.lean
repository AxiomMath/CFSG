module

public import Certificates.Data.Kernel.HNLocalK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HNLocal "Certificates/Data/Kernel/HNLocal/data/w.items.gz" 24384 737329757262459952
    V0 (W 0 4) SWN
#kc_select CFSG.KD.HNLocal WC W 4

public section

namespace CFSG.KD.HNLocal

@[expose] noncomputable def SW (m : Nat) : Nat := Nat.shiftRight SWN (Nat.mul (nat_lit 2793) m)

end CFSG.KD.HNLocal

end
