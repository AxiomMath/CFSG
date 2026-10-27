module

public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbTree
public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Outer3122 "Certificates/Kernel/BabyMonster/CTIB/data/outer3122.items.gz" 5257 2142717489889019168
  S E T

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Outer3122

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KD.Outer3122

@[expose] noncomputable def act (k x : Nat) : Nat := fuseK LOq AH6 Gs Ds k x

theorem inc : ∀ i < 64, incPt 64 8388608 S i = true := by lc_cover 64

theorem clos : ∀ i < 64, closPt act 37 64 S E i = true := by lc_cover 8

theorem tree : ∀ i < 64, treePt act 37 64 0 S T i = true := by lc_cover 64

theorem root : Nat.beq (fld32 S 0) 46090 = true := by quickRfl

theorem target : Nat.beq (fld32 S 32) 4204845 = true := by quickRfl

theorem neg_clos : notB (closPt act 37 64 S (Nat.xor E 1) 0) = true := by quickRfl

theorem neg_tree : notB (treePt act 37 64 0 S (Nat.xor T (Nat.shiftLeft 1 (Nat.add 32 12))) 1) = true := by
  quickRfl

theorem neg_inc : notB (incPt 64 46090 S 0) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB.Outer3122

end
