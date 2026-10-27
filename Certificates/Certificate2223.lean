module

public import CFSG.Sporadic.Schreier.PairHeCheckInputs
import Certificates.Kernel.SporSch.PairHe.Check2223

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairHe in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
open CFSG.Sporadic.HeldB in
theorem certificate2223 : (ordB bs wA 2 = true ∧ ordB bs wB 7 = true ∧ ordB bs (patW wA wB [false, true]) 17 = true ∧
      ordB bs (patW wA wB commPat) 6 = true ∧ ordB bs (patW wA wB pat12) 12 = true ∧
      ordB bs (patW wA wB pat15) 15 = true
    )
    ∧ (heBlocks.map Array.size = [8330, 4480, 108])
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK CFSG.Sporadic.Schreier.PairHe.levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 8330 CFSG.Sporadic.Schreier.PairHe.levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size) = [24990, 187425]
    ) := KernelSporSch.PHeCheck.facts

end Certificates
