module

public import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public import Certificates.Certificate2241

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def groups : List (List Nat) := [[0], [1], [2, 3, 4]]

@[expose] def blocks : List (Array (Array Nat)) := blocksOf 275 levels groups

@[expose] def conds : List (List Bool × Nat) := [([false, true], 11), (commPat, 5)]

theorem chain_check :
    rawChainOK 275 (mclStrongArrs.extract 0 2) mclStrongArrs baseArr mclWords 4 = true ∧
      rawOrbitSizes 275 mclStrongArrs baseArr = [275, 112, 81, 45, 8] :=
  Certificates.certificate2241.1

theorem word_orders :
    ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true :=
  Certificates.certificate2241.2.1

theorem classes :
    (∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 275 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 22275 :=
  Certificates.certificate2241.2.2

end CFSG.Sporadic.Schreier.PairMcL
