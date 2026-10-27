
module

public import CFSG.Quasithin.H13.A5M12SylInputs
import Certificates.Kernel.HMathieu.RootsPair
import CFSG.Certificates.Kernel.HMathieu.OfGensPairSound
import CFSG.Certificates.Kernel.HMathieu.OddSound
public import CFSG.Quasithin.Background.HMathieuPT24

set_option maxRecDepth 400000

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 in
public theorem certificate7112 :
    (T12s2.check = true ∧ T12s2.n = 128 ∧ T12s2.allOK okPair = true)
    ∧ (T12s3.check = true ∧ T12s3.n = 27 ∧ T12s3.allOK okPair = true)
    ∧ (T12s5.check = true ∧ T12s5.n = 5 ∧ T12s5.allOK okPair = true)
    ∧ (T12s11.check = true ∧ T12s11.n = 11 ∧ T12s11.allOK okPair = true) := by
  have r0 : rootPairK 12 T12.gens T12.E = true := RootsPair.c7112roots0
  have r1 : rootPairK 12 (Odd.G.getD 14 []) (Odd.E.getD 14 []) = true := RootsPair.c7112roots1
  have r2 : rootPairK 12 (Odd.G.getD 15 []) (Odd.E.getD 15 []) = true := RootsPair.c7112roots2
  have r3 : rootPairK 12 (Odd.G.getD 16 []) (Odd.E.getD 16 []) = true := RootsPair.c7112roots3
  have h1 : oddOK κC12Cols lift12Cols 10 6 32 (Odd.G.getD 14 []) (Odd.E.getD 14 [])
    (Odd.J.getD 14 []) = true := Odd.oddK14
  have h2 : oddOK κC12Cols lift12Cols 10 6 16 (Odd.G.getD 15 []) (Odd.E.getD 15 [])
    (Odd.J.getD 15 []) = true := Odd.oddK15
  have h3 : oddOK κC12Cols lift12Cols 10 6 16 (Odd.G.getD 16 []) (Odd.E.getD 16 [])
    (Odd.J.getD 16 []) = true := Odd.oddK16
  exact ⟨ok_pair_of_rootPairK (by unfold T12s2; congr 1) r0 T12.bfs (by decide +kernel),
    ok_pair_of_rootPairK (by unfold T12s3; congr 1) r1 (oddOK_spec h1).1 (by decide +kernel),
    ok_pair_of_rootPairK (by unfold T12s5; congr 1) r2 (oddOK_spec h2).1 (by decide +kernel),
    ok_pair_of_rootPairK (by unfold T12s11; congr 1) r3 (oddOK_spec h3).1 (by decide +kernel)⟩

end Certificates
