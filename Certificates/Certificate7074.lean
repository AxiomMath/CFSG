
module


public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
import Certificates.Kernel.HMathieu.Roots
import CFSG.Certificates.Kernel.HMathieu.OfGensSound
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.Monster.Code
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
open CFSG.QuasithinUnique.Setup.X1 in
public theorem certificate7074 :
    (T24s2.check = true ∧ T24s2.n = 1024 ∧ T24s2.allOK okAut = true)
    ∧ (T24s3.check = true ∧ T24s3.n = 27 ∧ T24s3.allOK okAut = true)
    ∧ (T24s5.check = true ∧ T24s5.n = 5 ∧ T24s5.allOK okAut = true)
    ∧ (T24s7.check = true ∧ T24s7.n = 7 ∧ T24s7.allOK okAut = true)
    ∧ (T24s11.check = true ∧ T24s11.n = 11 ∧ T24s11.allOK okAut = true)
    ∧ (T24s23.check = true ∧ T24s23.n = 23 ∧ T24s23.allOK okAut = true) := by
  have r5 : rootK 0 12 (Odd.G.getD 5 []) (Odd.E.getD 5 []) = true := Roots.c7074roots5
  have r6 : rootK 0 12 (Odd.G.getD 6 []) (Odd.E.getD 6 []) = true := Roots.c7074roots6
  have r7 : rootK 0 12 (Odd.G.getD 7 []) (Odd.E.getD 7 []) = true := Roots.c7074roots7
  have r8 : rootK 0 12 (Odd.G.getD 8 []) (Odd.E.getD 8 []) = true := Roots.c7074roots8
  have r9 : rootK 0 12 (Odd.G.getD 9 []) (Odd.E.getD 9 []) = true := Roots.c7074roots9
  have r16 : rootK 0 12 T24.gens T24.E = true := Roots.c7074roots16
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
  exact ⟨ok_aut_of_rootK (by unfold T24s2; congr 1) r16 T24.bfs (by decide +kernel),
    ok_aut_of_rootK (by unfold T24s3; congr 1) r5 (oddOK_spec h5).1 (by decide +kernel),
    ok_aut_of_rootK (by unfold T24s5; congr 1) r6 (oddOK_spec h6).1 (by decide +kernel),
    ok_aut_of_rootK (by unfold T24s7; congr 1) r7 (oddOK_spec h7).1 (by decide +kernel),
    ok_aut_of_rootK (by unfold T24s11; congr 1) r8 (oddOK_spec h8).1 (by decide +kernel),
    ok_aut_of_rootK (by unfold T24s23; congr 1) r9 (oddOK_spec h9).1 (by decide +kernel)⟩

end Certificates
