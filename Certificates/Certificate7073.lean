module

public import CFSG.Quasithin.Background.HMathieuSyl23
import Certificates.Kernel.HMathieu.OddFix
import CFSG.Certificates.Kernel.HMathieu.FixListSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
public theorem certificate7073 :
    
      odd23OK T23s3 mats23s3 ∧ odd23OK T23s5 mats23s5 ∧ odd23OK T23s7 mats23s7 ∧
      odd23OK T23s11 mats23s11 ∧ odd23OK T23s23 mats23s23 := by
  have h0 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 0 []) (Odd.E.getD 0 []) (Odd.J.getD 0 []) =
    true := Odd.oddK0
  have h1 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 1 []) (Odd.E.getD 1 []) (Odd.J.getD 1 []) =
    true := Odd.oddK1
  have h2 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 2 []) (Odd.E.getD 2 []) (Odd.J.getD 2 []) =
    true := Odd.oddK2
  have h3 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 3 []) (Odd.E.getD 3 []) (Odd.J.getD 3 []) =
    true := Odd.oddK3
  have h4 : oddOK κCCols liftCCols 11 6 32 (Odd.G.getD 4 []) (Odd.E.getD 4 []) (Odd.J.getD 4 []) =
    true := Odd.oddK4
  have f0 : fixAllK (o2OK o2Masks23) ccECols liftECols 11 ((Odd.E.getD 0 []).drop 1)
    (OddFix.J.getD 0 []) (OddFix.R.getD 0 []) = true := OddFix.c7073fix0
  have f1 : fixAllK (o2OK o2Masks23) ccECols liftECols 11 ((Odd.E.getD 1 []).drop 1)
    (OddFix.J.getD 1 []) (OddFix.R.getD 1 []) = true := OddFix.c7073fix1
  have f2 : fixAllK (o2OK o2Masks23) ccECols liftECols 11 ((Odd.E.getD 2 []).drop 1)
    (OddFix.J.getD 2 []) (OddFix.R.getD 2 []) = true := OddFix.c7073fix2
  have f3 : fixAllK (o2OK o2Masks23) ccECols liftECols 11 ((Odd.E.getD 3 []).drop 1)
    (OddFix.J.getD 3 []) (OddFix.R.getD 3 []) = true := OddFix.c7073fix3
  have f4 : fixAllK (o2OK o2Masks23) ccECols liftECols 11 ((Odd.E.getD 4 []).drop 1)
    (OddFix.J.getD 4 []) (OddFix.R.getD 4 []) = true := OddFix.c7073fix4
  exact ⟨fixAll_of (mats := mats23s3) (by unfold T23s3; congr 1) h0 f0 rfl,
    fixAll_of (mats := mats23s5) (by unfold T23s5; congr 1) h1 f1 rfl,
    fixAll_of (mats := mats23s7) (by unfold T23s7; congr 1) h2 f2 rfl,
    fixAll_of (mats := mats23s11) (by unfold T23s11; congr 1) h3 f3 rfl,
    fixAll_of (mats := mats23s23) (by unfold T23s23; congr 1) h4 f4 rfl⟩

end Certificates
