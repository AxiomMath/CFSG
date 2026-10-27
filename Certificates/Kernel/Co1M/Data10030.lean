module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Co1M "Certificates/Kernel/Co1M/data/d10030.items.gz" 14806 7105969765183148497
  ESC EF0 ETA EXA[] EYA[] EBAa[] EBAc[] EDA EMA EPAa[] EPAc[] ETC EXC[] EYC[] EBCa[] EBCc[] EDC EMC
  EPCa[] EPCc[]

public section

namespace CFSG.KD.Co1M

@[expose] noncomputable def EBA : List (Nat × Nat) := List.zip EBAa EBAc

@[expose] noncomputable def EPA : List (Nat × Nat) := List.zip EPAa EPAc

@[expose] noncomputable def EBC : List (Nat × Nat) := List.zip EBCa EBCc

@[expose] noncomputable def EPC : List (Nat × Nat) := List.zip EPCa EPCc

end CFSG.KD.Co1M

end
