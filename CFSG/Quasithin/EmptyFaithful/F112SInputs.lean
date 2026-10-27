module

public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Quasithin.F112S

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def isInv (a : Array ℕ) : Bool :=
  eqA 1755 (compA 1755 a a) (idA 1755) && !(eqA 1755 a (idA 1755))

@[expose] def invs : Array (Array ℕ) := (survivors5 1755 titsSLevels isInv).toArray

@[expose] def numInvs : ℕ := invs.size

@[expose] def prodIdx (i j : ℕ) : ℕ :=
  let p := compA 1755 invs[i]! invs[j]!
  ((List.range numInvs).find? fun k => eqA 1755 p invs[k]!).getD numInvs

@[expose] def prodTab : Array (Array ℕ) :=
  Array.ofFn (n := numInvs) fun i => Array.ofFn (n := numInvs) fun j => prodIdx i j

@[expose] def prodAt (i j : ℕ) : ℕ := (prodTab[i]!)[j]!

@[expose] def search (N : ℕ) (mulT : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, sp, lo =>
    (List.range N).all fun y =>
      decide (y < lo) || sp.contains y ||
        !(sp.all fun s => decide (mulT y s < N)) ||
        !(sp.all fun s => decide (y ≤ mulT y s)) ||
        search N mulT f (y :: (sp ++ sp.map (mulT y))) (y + 1)

@[expose] def invsOK : Bool :=
  invs.all fun a => isInvA 1755 a (invCand 1755 a) && isInv a

@[expose] def invsDistinct : Bool :=
  allLt numInvs fun i => allLt numInvs fun j => decide (i = j) || !(eqA 1755 invs[i]! invs[j]!)

@[expose] def invsComplete : Bool :=
  all5 1755 titsSLevels fun a =>
    !(isInv a) || (List.range numInvs).any fun i => eqA 1755 a invs[i]!

@[expose] def outerOK : Bool :=
  all5 1755 titsSLevels fun a =>
    !(eqA 1755 (compA 1755 (compA 1755 a titsPiArr) (compA 1755 a titsPiArr)) (idA 1755))

@[expose] def TitsRankCheck : Prop :=
  invsOK = true ∧ invsDistinct = true ∧ invsComplete = true ∧
    search numInvs prodAt 6 [] 0 = true ∧ outerOK = true

instance : Decidable TitsRankCheck :=
  inferInstanceAs (Decidable (invsOK = true ∧ invsDistinct = true ∧ invsComplete = true ∧
    search numInvs prodAt 6 [] 0 = true ∧ outerOK = true))

end CFSG.Quasithin.F112S
