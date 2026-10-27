module

public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.Pair.McLCheckP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairMcL in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2241 : (rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8]
    )
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true
    )
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 275 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 22275
    ) := KernelSporSch.PMcLCheck.facts_proved

end Certificates
