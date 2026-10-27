module

public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import Certificates.Kernel.SporSch.Pair.J2Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ2 in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2234 : (rawChainOK 315 (j2StrongArrs.extract 0 2) j2StrongArrs baseArr j2Words 1 = true ∧
      rawOrbitSizes 315 j2StrongArrs baseArr = [315, 160, 12]
    )
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
      ordB bs (patW wA wB commPat) 12 = true
    )
    ∧ (countW (fun w => ordB bs w 2) blocks [] = 2835 ∧
      countW (fun w => ordB bs w 3) blocks [] = 17360
    )
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK CFSG.Sporadic.Schreier.PairJ2.levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 315 CFSG.Sporadic.Schreier.PairJ2.levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 2835
    )
    ∧ ((cl.map fun c => c.2.1.size *
      countW (fun y => ordB bs y 3 && condsOK bs c.1 y conds) blocks []).sum = 1209600
    ) := KernelSporSch.PJ2Facts.facts

end Certificates
