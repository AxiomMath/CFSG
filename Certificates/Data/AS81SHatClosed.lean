module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs

public section

namespace CFSG.ComponentClassification.AS81.SHatClosed

open CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.Census

@[expose] def fixCount (t : Tab) : Nat := countBelow 64 fun i => (t[i]! == i)

@[expose] def fixCount4 (t₁ t₂ t₃ t₄ : Tab) : Nat :=
  countBelow 64 fun i => (t₁[i]! == i) && (t₂[i]! == i) && (t₃[i]! == i) && (t₄[i]! == i)

@[expose] def isInvol (t : Tab) : Bool := comp 64 t t == idTab 64 && !(t == idTab 64)

@[expose] def invL : Array Tab := lEnum.tabs.filter isInvol

@[expose] def commMat : Array (Array Bool) :=
  invL.map fun a => invL.map fun b => comp 64 a b == comp 64 b a

@[expose] def cm (i j : Nat) : Bool := (commMat[i]!)[j]!

@[expose] def span2 (a b : Tab) : Array Tab := #[a, b, comp 64 a b]

@[expose] def span3 (a b c : Tab) : Array Tab :=
  span2 a b ++ #[c] ++ (span2 a b).map fun x => comp 64 x c

@[expose] def centIdx : Array (Array Nat) :=
  (Array.range invL.size).map fun i => (Array.range invL.size).filter fun j => cm i j

@[expose] def f1OK : Bool := invL.all fun t => fixCount t == 16

@[expose] def f2OK : Bool :=
  allBelow invL.size fun i =>
    let a := invL[i]!
    let ci := centIdx[i]!
    ci.all fun j =>
      invL[j]! == a ||
        (let s₂ := span2 a invL[j]!
         ci.all fun k =>
           !(cm j k) || s₂.contains invL[k]! ||
             (let s₃ := span3 a invL[j]! invL[k]!
              ci.all fun l =>
                !(cm j l && cm k l) || s₃.contains invL[l]! ||
                  (ci.filter fun m => cm j m && cm k m && cm l m).size == 15))

@[expose] def f3OK : Bool :=
  allBelow invL.size fun i =>
    let a := invL[i]!
    let ci := centIdx[i]!
    ci.all fun j =>
      invL[j]! == a ||
        (let s₂ := span2 a invL[j]!
         ci.all fun k =>
           !(cm j k) || s₂.contains invL[k]! ||
             (let s₃ := span3 a invL[j]! invL[k]!
              ci.all fun l =>
                !(cm j l && cm k l) || s₃.contains invL[l]! ||
                  fixCount4 a invL[j]! invL[k]! invL[l]! == 2))

end CFSG.ComponentClassification.AS81.SHatClosed
