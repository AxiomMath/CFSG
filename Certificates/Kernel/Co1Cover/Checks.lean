
module

public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Data.Kernel.Co1F2
public import CFSG.Sporadic.Co1.Cover.Data
public import CFSG.Sporadic.Co1.Module.FormsInputs
public import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

set_option maxRecDepth 100000

#ks_chars CertificateChecks.KernelCo1Cover.SeedA CFSG.Sporadic.Co1.Native.seedA

#ks_chars CertificateChecks.KernelCo1Cover.SeedB CFSG.Sporadic.Co1.Native.seedB

namespace CertificateChecks.KernelCo1Cover

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT

theorem seedA_bind : m1Bind SeedA.chars 24 R0 = true := by quickRfl

theorem seedB_bind : m1Bind SeedB.chars 24 R1 = true := by quickRfl

theorem prog_ok : progK 24 R CFSG.Sporadic.Co1.Cover.covProg 2 = true := by quickRfl

theorem inv4_ok : invK 24 R4 I4 k4 = true := by quickRfl

theorem inv5_ok : invK 24 R5 I5 k5 = true := by quickRfl

theorem rel24_ok : relCheckK 24 R4 R5 I4 I5 CFSG.KBAlt.M24.rels = true := by quickRfl

theorem packA_ok : packB 11 CFSG.Sporadic.Co1.Cover.Aa.toList AaP = true := by quickRfl

theorem packB_ok : packB 11 CFSG.Sporadic.Co1.Cover.Ba.toList BaP = true := by quickRfl

theorem bb_ok : Nat.beq (mulF 11 BaP BaP) BBP = true := by quickRfl

theorem rel11_ok : relCheckK 11 AaP BaP AaP BBP CFSG.KBAlt.M24.rels = true := by quickRfl

theorem trA_ok : Nat.beq (trK 11 AaP) TAP = true := by quickRfl

theorem trB_ok : Nat.beq (trK 11 BaP) TBP = true := by quickRfl

theorem basic_ok : epsBasicK E = true := by quickRfl

theorem inj_ok : epsInjK E = true := by quickRfl

theorem normA_ok : normK E R4 TAP = true := by quickRfl

theorem normB_ok : normK E R5 TBP = true := by quickRfl

theorem eprod_ok : Nat.beq (eprodK E 722) EPP = true := by quickRfl

theorem t0_ok : Nat.beq (mulF 24 EPP R4) T0P = true := by quickRfl

theorem t0_order : orderIsK 24 T0P 2 = true := by quickRfl

theorem trT0_ok : Nat.beq (trK 24 T0P) T0tP = true := by quickRfl

theorem packQ_ok : packB 24 CFSG.Sporadic.Co1.Module.qRows.toList QP = true := by quickRfl

theorem trQ_ok : Nat.beq (trK 24 QP) QtP = true := by quickRfl

theorem fix_ok : fixK 24 T0tP QtP F Y 12 4096 0 = true := by quickRfl

theorem lenE : lenL E = 11 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem noncomm_ok :
    notB (Nat.beq (fget (mulF 24 R4 R5) ndiff 24) (fget (mulF 24 R5 R4) ndiff 24)) = true := by
  quickRfl

end CertificateChecks.KernelCo1Cover

end
