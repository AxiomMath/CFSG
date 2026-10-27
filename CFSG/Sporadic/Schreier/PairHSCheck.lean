module

public import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public import Certificates.Certificate2219

public section

namespace CFSG.Sporadic.Schreier.PairHS

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def groups : List (List Nat) := [[0], [1], [2, 3]]

@[expose] def blocks : List (Array (Array Nat)) := blocksOf 3850 levels groups

@[expose] def parCount (f : List (Array Nat) → Bool) : List (Array (Array Nat)) → Nat
  | [] => countW f [] []
  | B :: Bs => countWPar 250 f B Bs

@[expose] def conds : List (List Bool × Nat) := [([false, true], 11), (commPat, 5)]

theorem chain_check :
    rawChainOK 3850 (hsStrongArrs.extract 0 2) hsStrongArrs baseArr hsWords 4 = true ∧
      rawOrbitSizes 3850 hsStrongArrs baseArr = [3850, 960, 6, 2] :=
  Certificates.certificate2219.1

theorem word_orders :
    ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true :=
  Certificates.certificate2219.2.1

theorem classes :
    (∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 3850 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 21175 :=
  Certificates.certificate2219.2.2

end CFSG.Sporadic.Schreier.PairHS
