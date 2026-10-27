module

import Certificates.Kernel.HMathieu.OddFix
import CFSG.Certificates.Kernel.HMathieu.FixListSound
import CFSG.Certificates.Kernel.HMathieu.AvoidSound
public import CFSG.Quasithin.Background.HMathieuSyl24Base

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.Monster.Code
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
public theorem certificate7076 :
    
      odd24OK T24s3 mats24s3 ∧ odd24OK T24s5 mats24s5 ∧ odd24OK T24s7 mats24s7 ∧
      odd24OK T24s11 mats24s11 ∧ odd24OK T24s23 mats24s23 := by
  have e : avoidK 11 3 o2Masks24 = avoidOK 11 3 o2Masks24 :=
    funext fun F => (avoidOK_eq 3 o2Masks24 F).symm
  have h5 : oddOK κCCols liftCCols 11 6 32 (Odd.G.getD 5 []) (Odd.E.getD 5 [])
    (Odd.J.getD 5 []) = true := Odd.oddK5
  have h6 : oddOK κCCols liftCCols 11 7 16 (Odd.G.getD 6 []) (Odd.E.getD 6 [])
    (Odd.J.getD 6 []) = true := Odd.oddK6
  have h7 : oddOK κCCols liftCCols 11 7 16 (Odd.G.getD 7 []) (Odd.E.getD 7 [])
    (Odd.J.getD 7 []) = true := Odd.oddK7
  have h8 : oddOK κCCols liftCCols 11 7 16 (Odd.G.getD 8 []) (Odd.E.getD 8 [])
    (Odd.J.getD 8 []) = true := Odd.oddK8
  have h9 : oddOK κCCols liftCCols 11 7 32 (Odd.G.getD 9 []) (Odd.E.getD 9 [])
    (Odd.J.getD 9 []) = true := Odd.oddK9
  have f5 : fixAllK (avoidK 11 3 o2Masks24) ccECols liftECols 11 ((Odd.E.getD 5 []).drop 1)
    (OddFix.J.getD 5 []) (OddFix.R.getD 5 []) = true := OddFix.c7073fix5
  have f6 : fixAllK (avoidK 11 3 o2Masks24) ccECols liftECols 11 ((Odd.E.getD 6 []).drop 1)
    (OddFix.J.getD 6 []) (OddFix.R.getD 6 []) = true := OddFix.c7073fix6
  have f7 : fixAllK (avoidK 11 3 o2Masks24) ccECols liftECols 11 ((Odd.E.getD 7 []).drop 1)
    (OddFix.J.getD 7 []) (OddFix.R.getD 7 []) = true := OddFix.c7073fix7
  have f8 : fixAllK (avoidK 11 3 o2Masks24) ccECols liftECols 11 ((Odd.E.getD 8 []).drop 1)
    (OddFix.J.getD 8 []) (OddFix.R.getD 8 []) = true := OddFix.c7073fix8
  have f9 : fixAllK (avoidK 11 3 o2Masks24) ccECols liftECols 11 ((Odd.E.getD 9 []).drop 1)
    (OddFix.J.getD 9 []) (OddFix.R.getD 9 []) = true := OddFix.c7073fix9
  rw [e] at f5 f6 f7 f8 f9
  exact ⟨fixAll_of (mats := mats24s3) (by unfold T24s3; congr 1) h5 f5 rfl,
    fixAll_of (mats := mats24s5) (by unfold T24s5; congr 1) h6 f6 rfl,
    fixAll_of (mats := mats24s7) (by unfold T24s7; congr 1) h7 f7 rfl,
    fixAll_of (mats := mats24s11) (by unfold T24s11; congr 1) h8 f8 rfl,
    fixAll_of (mats := mats24s23) (by unfold T24s23; congr 1) h9 f9 rfl⟩

end Certificates
