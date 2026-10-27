module

public import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHeCheckInputs
public import Certificates.Certificate2223

public section

namespace CFSG.Sporadic.Schreier.PairHe

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.HeldB

@[expose] def conds : List (List Bool × Nat) :=
  [([false, true], 17), (commPat, 6), (pat12, 12), (pat15, 15)]

@[expose] def t1Arr : Array Nat := Array.ofFn fun p : Fin 8330 => evR wT p.val

@[expose] def wT1 : List (Array Nat) := [t1Arr]

theorem word_orders :
    ordB bs wA 2 = true ∧ ordB bs wB 7 = true ∧ ordB bs (patW wA wB [false, true]) 17 = true ∧
      ordB bs (patW wA wB commPat) 6 = true ∧ ordB bs (patW wA wB pat12) 12 = true ∧
      ordB bs (patW wA wB pat15) 15 = true :=
  Certificates.certificate2223.1

theorem block_sizes : heBlocks.map Array.size = [8330, 4480, 108] :=
  Certificates.certificate2223.2.1

theorem classes :
    (∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 8330 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size) = [24990, 187425] :=
  Certificates.certificate2223.2.2

end CFSG.Sporadic.Schreier.PairHe
