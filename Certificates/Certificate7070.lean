module

import Certificates.Kernel.HMathieu.OddFix
import CFSG.Certificates.Kernel.HMathieu.FixListSound
public import CFSG.Quasithin.Background.HMathieuSyl22Base

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.Monster.Code
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
public theorem certificate7070 :
    
      odd22OK T22s3 mats22s3 ∧ odd22OK T22s5 mats22s5 ∧ odd22OK T22s7 mats22s7 ∧
      odd22OK T22s11 mats22s11 := by
  have h10 : oddOK κC22Cols lift22Cols 10 6 16 (Odd.G.getD 10 []) (Odd.E.getD 10 [])
    (Odd.J.getD 10 []) = true := Odd.oddK10
  have h11 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 11 []) (Odd.E.getD 11 [])
    (Odd.J.getD 11 []) = true := Odd.oddK11
  have h12 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 12 []) (Odd.E.getD 12 [])
    (Odd.J.getD 12 []) = true := Odd.oddK12
  have h13 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 13 []) (Odd.E.getD 13 [])
    (Odd.J.getD 13 []) = true := Odd.oddK13
  have f10 : fixAllK (o2OK o2Masks22) cc10Cols lift10Cols 10 ((Odd.E.getD 10 []).drop 1)
    (OddFix.J.getD 10 []) (OddFix.R.getD 10 []) = true := OddFix.c7073fix10
  have f11 : fixAllK (o2OK o2Masks22) cc10Cols lift10Cols 10 ((Odd.E.getD 11 []).drop 1)
    (OddFix.J.getD 11 []) (OddFix.R.getD 11 []) = true := OddFix.c7073fix11
  have f12 : fixAllK (o2OK o2Masks22) cc10Cols lift10Cols 10 ((Odd.E.getD 12 []).drop 1)
    (OddFix.J.getD 12 []) (OddFix.R.getD 12 []) = true := OddFix.c7073fix12
  have f13 : fixAllK (o2OK o2Masks22) cc10Cols lift10Cols 10 ((Odd.E.getD 13 []).drop 1)
    (OddFix.J.getD 13 []) (OddFix.R.getD 13 []) = true := OddFix.c7073fix13
  exact ⟨fixAll_of (mats := mats22s3) (by unfold T22s3; congr 1) h10 f10 rfl,
    fixAll_of (mats := mats22s5) (by unfold T22s5; congr 1) h11 f11 rfl,
    fixAll_of (mats := mats22s7) (by unfold T22s7; congr 1) h12 f12 rfl,
    fixAll_of (mats := mats22s11) (by unfold T22s11; congr 1) h13 f13 rfl⟩

end Certificates
