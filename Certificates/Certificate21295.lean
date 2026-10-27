module

public import CFSG.LargeExtraspecial.AS35WJ2Data
import CFSG.Certificates.Kernel.BfsPinAlg
import Certificates.Kernel.SchreierFam.J2UN
import Certificates.Kernel.Census.J2H.Checks

public section

namespace CertificateChecks.Batch21295

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
  CFSG.Monster.B.Co2.Native

variable {n w : Nat}

private theorem foldr_unpack {A B : Nat} (hsz : szOK n w = true) (hA : PP n w A) (hB : PP n w B) :
    ∀ l : List Bool,
      PP n w ((l.map fun b => if b then B else A).foldr (pcomp n w (mask w)) (pidn n w)) ∧
      (l.map fun b => if b then unpack n w B else unpack n w A).foldr (compA n) (idA n) =
        unpack n w ((l.map fun b => if b then B else A).foldr (pcomp n w (mask w)) (pidn n w))
  | [] => ⟨PP.id hsz, idA_eq hsz⟩
  | b :: l => by
    obtain ⟨h1, h2⟩ := foldr_unpack hsz hA hB l
    cases b
    · simp only [List.map_cons, List.foldr_cons, Bool.false_eq_true, ↓reduceIte, h2]
      exact ⟨hA.mul h1, compA_PP hA h1⟩
    · simp only [List.map_cons, List.foldr_cons, ↓reduceIte, h2]
      exact ⟨hB.mul h1, compA_PP hB h1⟩

end CertificateChecks.Batch21295

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
  CFSG.Monster.B.Co2.Native CFSG.LargeExtraspecial.AS35W CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.J2Data CertificateChecks.KernelJ2Cover
  CertificateChecks.KernelSchreierFam CertificateChecks.KernelJ2H

theorem certificate21295 : CFSG.LargeExtraspecial.AS35W.j2ConjCheck = true := by
  have hsz : szOK 315 9 = true := by decide +kernel
  have ha : autStrong[0]! = unpack 315 9 (PA.S 0) := binds.2.2.2.2.1 0 (by norm_num)
  have hb : autStrong[1]! = unpack 315 9 (PA.S 1) := binds.2.2.2.2.1 1 (by norm_num)
  have hu : uStrong[0]! = unpack 315 9 (JU.S 0) := J2.uS 0 (by norm_num)
  have ht : twoAArr = unpack 315 9 (S0C.S 0) := arrBind_sound s0_z
  have pA : PP 315 9 (PA.S 0) := PP_of_permOK hsz (by decide +kernel)
  have pB : PP 315 9 (PA.S 1) := PP_of_permOK hsz (by decide +kernel)
  have pU : PP 315 9 (JU.S 0) := PP_of_permOK hsz (by decide +kernel)
  have pT : PP 315 9 (S0C.S 0) := PP_of_permOK hsz (by decide +kernel)
  obtain ⟨pC, hC⟩ := CertificateChecks.Batch21295.foldr_unpack hsz pA pB j2Word
  unfold j2ConjCheck j2CArr
  rw [ha, hb, hC, hu, ht, compA_PP pC pT, compA_PP pU pC, eqA_PP (pC.mul pT) (pU.mul pC),
    eqA_PP pU pT]
  decide +kernel

end Certificates
