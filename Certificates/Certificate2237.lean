module

public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairJ3.Check2237

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2237 : (rawChainOK 6156 (j3StrongArrs.extract 0 2) j3StrongArrs CFSG.Sporadic.Schreier.PairJ3.baseArr j3Words 4 = true ∧
      rawOrbitSizes 6156 j3StrongArrs CFSG.Sporadic.Schreier.PairJ3.baseArr = [6156, 1360, 2, 3]
    )
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 19 = true ∧
      ordB bs (patW wA wB commPat) 9 = true
    )
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 6156 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 26163
    ) := KernelSporSch.PJ3Check.facts

end Certificates
