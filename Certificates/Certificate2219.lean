module

public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import Certificates.Kernel.SporSch.PairHS.Check2219
import CFSG.Sporadic.Presentation.Common
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.CosetTablePresented
import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairHS in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2219 : (rawChainOK 3850 (hsStrongArrs.extract 0 2) hsStrongArrs CFSG.Sporadic.Schreier.PairHS.baseArr hsWords 4 = true ∧
      rawOrbitSizes 3850 hsStrongArrs CFSG.Sporadic.Schreier.PairHS.baseArr = [3850, 960, 6, 2]
    )
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true
    )
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 3850 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 21175
    ) := KernelSporSch.PHSCheck.facts

end Certificates
