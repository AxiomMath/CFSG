module

public import Certificates.Kernel.Co1B.Tabs131301
public import Certificates.Kernel.Co1B.Text131301
public import Certificates.Data.Kernel.Co1BS0
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.S0131301

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1BS0 CFSG.KC.Co1B CFSG.KLie.CT

theorem kGood : (good131R OT.chars && good131R PT.chars && good131R LT.chars) = true := by quickRfl
theorem kInv : (eqK (mulWK (RG 1) (RG 2)) oneK && eqK (RG 2) (mulWK (RG 1) (RG 1))) = true := by
  quickRfl
theorem kOps : (Nat.beq (pairsL (nums131R OT.chars 0 false)).length 1153 &&
    opsK RG (pairsL (nums131R OT.chars 0 false)) 0) = true := by quickRfl
theorem kPar : (Nat.beq (pairsL (nums131R PT.chars 0 false)).length 19683 &&
    parK LG131 (pairsL (nums131R PT.chars 0 false)) 0) = true := by quickRfl
theorem kE0 : eqK (EG 0) oneK = true := by quickRfl
theorem kLeft : (Nat.beq (nums131R LT.chars 0 false).length 59049 &&
    leftK RG EG LG131 (nums131R LT.chars 0 false) 0) = true := by quickRfl
theorem kSort : sortK EG SG = true := by quickRfl

@[expose] noncomputable def cj131K (E : Nat → Nat) (c b : Nat) : Bool :=
  strictB (Nat.land c (nat_lit 32767)) fun a =>
    strictB (Nat.land (Nat.shiftRight c (nat_lit 15)) (nat_lit 32767)) fun h =>
      strictB (Nat.shiftRight c (nat_lit 30)) fun h' =>
        andB (Nat.blt a b) (andB (notB (Nat.beq a 0)) (andB (Nat.blt h nSK) (andB (Nat.blt h' nSK)
          (andB (eqK (mulWK (E h) (E h')) oneK) (andB (eqK (mulWK (E h') (E h)) oneK)
            (andB (eqK (mulWK (E b) (E h)) (mulWK (E h) (E a))) (cubeK E a)))))))

@[expose] noncomputable def kill131K (E W C : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun t => strictB (Nat.add lo t) fun b =>
    orB (Nat.beq b 0) (orB (notB (cubeK E b))
      (Bool.rec (motive := fun _ => Bool) (cj131K E (C b) b) (witK E W b) (Nat.beq (C b) 0)))

theorem kK0 : kill131K EG WG CJG 0 1024 = true := by quickRfl
theorem kK1 : kill131K EG WG CJG 1024 1024 = true := by quickRfl
theorem kK2 : kill131K EG WG CJG 2048 1024 = true := by quickRfl
theorem kK3 : kill131K EG WG CJG 3072 1024 = true := by quickRfl
theorem kK4 : kill131K EG WG CJG 4096 1024 = true := by quickRfl
theorem kK5 : kill131K EG WG CJG 5120 1024 = true := by quickRfl
theorem kK6 : kill131K EG WG CJG 6144 1024 = true := by quickRfl
theorem kK7 : kill131K EG WG CJG 7168 1024 = true := by quickRfl
theorem kK8 : kill131K EG WG CJG 8192 1024 = true := by quickRfl
theorem kK9 : kill131K EG WG CJG 9216 1024 = true := by quickRfl
theorem kK10 : kill131K EG WG CJG 10240 1024 = true := by quickRfl
theorem kK11 : kill131K EG WG CJG 11264 1024 = true := by quickRfl
theorem kK12 : kill131K EG WG CJG 12288 1024 = true := by quickRfl
theorem kK13 : kill131K EG WG CJG 13312 1024 = true := by quickRfl
theorem kK14 : kill131K EG WG CJG 14336 1024 = true := by quickRfl
theorem kK15 : kill131K EG WG CJG 15360 1024 = true := by quickRfl
theorem kK16 : kill131K EG WG CJG 16384 1024 = true := by quickRfl
theorem kK17 : kill131K EG WG CJG 17408 1024 = true := by quickRfl
theorem kK18 : kill131K EG WG CJG 18432 1024 = true := by quickRfl
theorem kK19 : kill131K EG WG CJG 19456 227 = true := by quickRfl

end CertificateChecks.KernelCo1B.S0131301

end
