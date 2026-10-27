module

public import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public import Certificates.Certificate2237

public section

namespace CFSG.Sporadic.Schreier.PairJ3

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def groups : List (List Nat) := [[0], [1], [2, 3]]

@[expose] def blocks : List (Array (Array Nat)) := blocksOf 6156 levels groups

@[expose] def parCount (f : List (Array Nat) → Bool) : List (Array (Array Nat)) → Nat
  | [] => countW f [] []
  | B :: Bs => countWPar 400 f B Bs

@[expose] def conds : List (List Bool × Nat) := [([false, true], 19), (commPat, 9)]

theorem chain_check :
    rawChainOK 6156 (j3StrongArrs.extract 0 2) j3StrongArrs baseArr j3Words 4 = true ∧
      rawOrbitSizes 6156 j3StrongArrs baseArr = [6156, 1360, 2, 3] :=
  Certificates.certificate2237.1

theorem word_orders :
    ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 19 = true ∧
      ordB bs (patW wA wB commPat) 9 = true :=
  Certificates.certificate2237.2.1

theorem classes :
    (∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 6156 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 26163 :=
  Certificates.certificate2237.2.2

end CFSG.Sporadic.Schreier.PairJ3
