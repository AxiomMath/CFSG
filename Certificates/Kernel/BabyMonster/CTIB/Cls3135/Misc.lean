module

public import Certificates.Kernel.BabyMonster.CTIB.Cls3135Data
public import Certificates.Kernel.BabyMonster.CTIB.Orb3135Data
public import Certificates.Kernel.BabyMonster.CTIB.Outer3122
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Cls3135

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbW CFSG.KD.Cls3135

@[expose] noncomputable def fixK (j : Nat) : Nat :=
  (fun e => mulQ LOq (qinvK LOq (autQ LOq AH6 e))
    (mulQ LOq (mulQ LOq (nthN Ds j) (autQ LOq (nthN Gs j) 10541)) e)) (nthN CFSG.KD.Orb3135.EC j)

theorem prods : andB (Nat.beq (qinvK LOq 10541) 4204845)
    (andB (Nat.beq (mulQ LOq 10541 854) 10875) (Nat.beq (mulQ LOq 4204845 10875) 854)) = true := by
  quickRfl

theorem ec_inv : ∀ j < 15,
    Nat.beq (qinvK LOq (nthN CFSG.KD.Orb3135.EC j)) (nthN CFSG.KD.Orb3135.EC j) = true := by
  lc_cover 15

theorem fix : ∀ j < 15, Nat.beq (fixK j) 10541 = true := by lc_cover 15

theorem chk854 : Nat.beq (frChk LOq AH6 4204845 10541 P1 P2 10875 W854) 2 = true := by quickRfl

theorem chk8 : ∀ i < 64, Nat.beq (frChk LOq AH6 4204845 10541 P1 P2 (fld32 CFSG.KD.Outer3122.S i)
    (fldB 96 64 [V8] i)) 1 = true := by lc_cover 16

theorem neg_chk854 : notB (Nat.beq (frChk LOq AH6 4204845 10541 P1 P2 10875
    (Nat.xor W854 (Nat.shiftLeft 1 31))) 2) = true := by quickRfl

theorem neg_fix : notB (Nat.beq ((fun e => mulQ LOq (qinvK LOq (autQ LOq AH6 e))
    (mulQ LOq (mulQ LOq (nthN Ds 0) (autQ LOq (nthN Gs 0) 10541)) e)) 4101) 10541) = true := by
  quickRfl

end CertificateChecks.KernelBM.CTIB.Cls3135

end
