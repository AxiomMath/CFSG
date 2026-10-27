module

public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
import Certificates.Kernel.HMathieu.Roots
import CFSG.Certificates.Kernel.HMathieu.OfGensSound
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.Monster.Code
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
open CFSG.QuasithinUnique.Setup.X1 in
public theorem certificate7071 :
    (T23s2.check = true ∧ T23s2.n = 128 ∧ T23s2.allOK okM23 = true)
    ∧ (T23s3.check = true ∧ T23s3.n = 9 ∧ T23s3.allOK okM23 = true)
    ∧ (T23s5.check = true ∧ T23s5.n = 5 ∧ T23s5.allOK okM23 = true)
    ∧ (T23s7.check = true ∧ T23s7.n = 7 ∧ T23s7.allOK okM23 = true)
    ∧ (T23s11.check = true ∧ T23s11.n = 11 ∧ T23s11.allOK okM23 = true)
    ∧ (T23s23.check = true ∧ T23s23.n = 23 ∧ T23s23.allOK okM23 = true) := by
  have r0 : rootK 1 12 (Odd.G.getD 0 []) (Odd.E.getD 0 []) = true := Roots.c7074roots0
  have r1 : rootK 1 12 (Odd.G.getD 1 []) (Odd.E.getD 1 []) = true := Roots.c7074roots1
  have r2 : rootK 1 12 (Odd.G.getD 2 []) (Odd.E.getD 2 []) = true := Roots.c7074roots2
  have r3 : rootK 1 12 (Odd.G.getD 3 []) (Odd.E.getD 3 []) = true := Roots.c7074roots3
  have r4 : rootK 1 12 (Odd.G.getD 4 []) (Odd.E.getD 4 []) = true := Roots.c7074roots4
  have r15 : rootK 1 12 T23.gens T23.E = true := Roots.c7074roots15
  have h0 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 0 []) (Odd.E.getD 0 [])
    (Odd.J.getD 0 []) = true := Odd.oddK0
  have h1 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 1 []) (Odd.E.getD 1 [])
    (Odd.J.getD 1 []) = true := Odd.oddK1
  have h2 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 2 []) (Odd.E.getD 2 [])
    (Odd.J.getD 2 []) = true := Odd.oddK2
  have h3 : oddOK κCCols liftCCols 11 6 16 (Odd.G.getD 3 []) (Odd.E.getD 3 [])
    (Odd.J.getD 3 []) = true := Odd.oddK3
  have h4 : oddOK κCCols liftCCols 11 6 32 (Odd.G.getD 4 []) (Odd.E.getD 4 [])
    (Odd.J.getD 4 []) = true := Odd.oddK4
  exact ⟨ok_m23_of_rootK (by unfold T23s2; congr 1) r15 T23.bfs (by decide +kernel),
    ok_m23_of_rootK (by unfold T23s3; congr 1) r0 (oddOK_spec h0).1 (by decide +kernel),
    ok_m23_of_rootK (by unfold T23s5; congr 1) r1 (oddOK_spec h1).1 (by decide +kernel),
    ok_m23_of_rootK (by unfold T23s7; congr 1) r2 (oddOK_spec h2).1 (by decide +kernel),
    ok_m23_of_rootK (by unfold T23s11; congr 1) r3 (oddOK_spec h3).1 (by decide +kernel),
    ok_m23_of_rootK (by unfold T23s23; congr 1) r4 (oddOK_spec h4).1 (by decide +kernel)⟩

end Certificates
