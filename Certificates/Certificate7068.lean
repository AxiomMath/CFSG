
module


public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
import Certificates.Kernel.HMathieu.Roots
import CFSG.Certificates.Kernel.HMathieu.OfGensSound
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.Monster.Code
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
open CFSG.QuasithinUnique.Setup.X1 in
public theorem certificate7068 :
    (T22s2.check = true ∧ T22s2.n = 256 ∧ T22s2.allOK okPlus = true)
    ∧ (T22s3.check = true ∧ T22s3.n = 9 ∧ T22s3.allOK okPlus = true)
    ∧ (T22s5.check = true ∧ T22s5.n = 5 ∧ T22s5.allOK okPlus = true)
    ∧ (T22s7.check = true ∧ T22s7.n = 7 ∧ T22s7.allOK okPlus = true)
    ∧ (T22s11.check = true ∧ T22s11.n = 11 ∧ T22s11.allOK okPlus = true) := by
  have r10 : rootK 2 12 (Odd.G.getD 10 []) (Odd.E.getD 10 []) = true := Roots.c7074roots10
  have r11 : rootK 2 12 (Odd.G.getD 11 []) (Odd.E.getD 11 []) = true := Roots.c7074roots11
  have r12 : rootK 2 12 (Odd.G.getD 12 []) (Odd.E.getD 12 []) = true := Roots.c7074roots12
  have r13 : rootK 2 12 (Odd.G.getD 13 []) (Odd.E.getD 13 []) = true := Roots.c7074roots13
  have r14 : rootK 2 12 T22.gens T22.E = true := Roots.c7074roots14
  have h10 : oddOK κC22Cols lift22Cols 10 6 16 (Odd.G.getD 10 []) (Odd.E.getD 10 [])
    (Odd.J.getD 10 []) = true := Odd.oddK10
  have h11 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 11 []) (Odd.E.getD 11 [])
    (Odd.J.getD 11 []) = true := Odd.oddK11
  have h12 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 12 []) (Odd.E.getD 12 [])
    (Odd.J.getD 12 []) = true := Odd.oddK12
  have h13 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 13 []) (Odd.E.getD 13 [])
    (Odd.J.getD 13 []) = true := Odd.oddK13
  exact ⟨ok_plus_of_rootK (by unfold T22s2 gens22s2; congr 1) r14 T22.bfs (by decide +kernel),
    ok_plus_of_rootK (by unfold T22s3; congr 1) r10 (oddOK_spec h10).1 (by decide +kernel),
    ok_plus_of_rootK (by unfold T22s5; congr 1) r11 (oddOK_spec h11).1 (by decide +kernel),
    ok_plus_of_rootK (by unfold T22s7; congr 1) r12 (oddOK_spec h12).1 (by decide +kernel),
    ok_plus_of_rootK (by unfold T22s11; congr 1) r13 (oddOK_spec h13).1 (by decide +kernel)⟩

end Certificates
