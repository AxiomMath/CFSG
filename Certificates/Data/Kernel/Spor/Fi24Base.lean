module

public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.CfgIFi24

public section

namespace CFSG.KC.Fi24Base

open CFSG.KC.Loop CFSG.Sporadic.Fi24.Native Timmesfeld.Fi24Cl
  CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg

@[expose] noncomputable def letF (f : Nat → Nat → Nat) (l x : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 26), f l x, nat_lit 0)

@[expose] noncomputable def apF (f : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (ih x) (fun y => letF f l y)) w x

@[expose] noncomputable def eqL (f : Nat → Nat → Nat) (u v : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (apF f u b) (apF f v b), ih))

@[expose] noncomputable def eqB (f : Nat → Nat → Nat) (u v : List Nat) : Bool :=
  eqL f u v chainBase.toList

@[expose] def cfgAtG (E : List Nat → List Nat → Bool) (i : Nat) : Bool :=
  (xWords[i]!).all (· < 26) && (nWords[i]!).all (· < 26) &&
  E (xWords[i]! ++ xWords[i]! ++ xWords[i]!) [] && !E xWords[i]! [] &&
  E (nWords[i]! ++ xWords[i]! ++ invWord nWords[i]!) (invWord xWords[i]!) &&
  (List.range 6).all fun j =>
    E (xWords[i]! ++ xWords[j]!) (xWords[j]! ++ xWords[i]!) &&
      (!decide (j < i) || E (nWords[i]! ++ xWords[j]! ++ invWord nWords[i]!) xWords[j]!)

@[expose] def cfgG (E : List Nat → List Nat → Bool) : Bool :=
  (List.range 6).all fun i => cfgAtG E i

@[expose] def invAtG (E : List Nat → List Nat → Bool) (r s t t' : List Nat) : Bool :=
  (s ++ t ++ t').all (· < 26) &&
  E (s ++ s) [] && E (s ++ r ++ s) (invWord r) &&
  E (t ++ t) [] && E (t' ++ t') [] &&
  E (t ++ r) (r ++ t) && E (t' ++ r) (r ++ t') &&
  E (t ++ t' ++ t ++ t' ++ t ++ t') [] && !E (t ++ t') []

@[expose] def invAtRepG (E : List Nat → List Nat → Bool) (i : Nat) : Bool :=
  invAtG E repWordsN[i]! invData[i]!.1 invData[i]!.2.1 invData[i]!.2.2

@[expose] def invG (E : List Nat → List Nat → Bool) : Bool :=
  invAtRepG E 0 && invAtRepG E 1 && invAtRepG E 2 && invAtRepG E 3 && invAtRepG E 4

end CFSG.KC.Fi24Base

end
