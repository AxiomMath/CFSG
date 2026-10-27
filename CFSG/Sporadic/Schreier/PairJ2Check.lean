module

public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import Certificates.Certificate2234

public section

namespace CFSG.Sporadic.Schreier.PairJ2

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem chain_check :
    rawChainOK 315 (j2StrongArrs.extract 0 2) j2StrongArrs baseArr j2Words 1 = true ∧
      rawOrbitSizes 315 j2StrongArrs baseArr = [315, 160, 12] :=
  Certificates.certificate2234.1

theorem word_orders :
    ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 7 = true ∧
      ordB bs (patW wA wB commPat) 12 = true :=
  Certificates.certificate2234.2.1

theorem counts :
    countW (fun w => ordB bs w 2) blocks [] = 2835 ∧
      countW (fun w => ordB bs w 3) blocks [] = 17360 :=
  Certificates.certificate2234.2.2.1

theorem classes :
    (∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 315 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 2835 :=
  Certificates.certificate2234.2.2.2.1

theorem total :
    (cl.map fun c => c.2.1.size *
      countW (fun y => ordB bs y 3 && condsOK bs c.1 y conds) blocks []).sum = 1209600 :=
  Certificates.certificate2234.2.2.2.2

end CFSG.Sporadic.Schreier.PairJ2
