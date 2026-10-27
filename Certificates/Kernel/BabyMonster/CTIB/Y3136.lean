module

public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbTree
public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Y3136 "Certificates/Kernel/BabyMonster/CTIB/data/y3136.items.gz" 45864 10509944385570019101
  Y[6] ST0[] ST1[] ST2[] ST3[] ST4[] ST5[] S E T W[5]

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Y3136

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KD.Y3136

@[expose] noncomputable def STs : List (List Nat) := [ST0, ST1, ST2, ST3, ST4, ST5]

@[expose] noncomputable def Ys : List Nat := [Y0, Y1, Y2, Y3, Y4, Y5]

@[expose] noncomputable def Fs : List Nat := [0, 16, 0, 0, 0, 0]

@[expose] noncomputable def act (j x : Nat) : Nat := yActK LOq Ys Fs j x

theorem words : ∀ j < 6, Nat.beq (wordKF Syms CTs (nthLL STs j) (id32 22)) (nthN Ys j) = true := by
  lc_cover 1

theorem fix7 : ∀ j < 6, Nat.beq (act j 7) 7 = true := by lc_cover 6

theorem inc : ∀ i < 2240, incPt 2240 8388608 S i = true := by lc_cover 560

theorem clos : ∀ i < 2240, closPt act 6 2240 S E i = true := by lc_cover 64

theorem tree : ∀ i < 2240, treePt act 6 2240 0 S T i = true := by lc_cover 280

theorem root : Nat.beq (fld32 S 0) 32 = true := by quickRfl

theorem neg_words : notB (Nat.beq (wordKF Syms CTs (nthLL STs 0) (id32 22)) (Nat.xor Y0 1)) = true := by
  quickRfl

theorem neg_clos : notB (closPt act 6 2240 S (Nat.xor E 1) 0) = true := by quickRfl

theorem neg_tree : notB (treePt act 6 2240 0 S (Nat.xor T (Nat.shiftLeft 1 (Nat.add 32 12))) 1) = true := by
  quickRfl

end CertificateChecks.KernelBM.CTIB.Y3136

end
