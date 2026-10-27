module

public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank

open CFSG.ONSchreier CFSG.PSL3Four.Native

@[expose] def invTabs (_ : Unit := ()) : Array Tab :=
  t32Enum.tabs.filter fun t => comp 32 t t == idTab 32 && !(t == idTab 32)

@[expose] def commMat (I : Array Tab) : Array (Array Bool) :=
  I.map fun a => I.map fun b => comp 32 a b == comp 32 b a

@[expose] def fourthOK (I : Array Tab) (C : Array (Array Bool)) (i j k : Nat) : Bool :=
  let a := I[i]!
  let b := I[j]!
  let c := I[k]!
  let ab := comp 32 a b
  let ac := comp 32 a c
  let bc := comp 32 b c
  let abc := comp 32 ab c
  allBelow I.size fun l =>
    !((C[i]!)[l]! && (C[j]!)[l]! && (C[k]!)[l]!) ||
      (I[l]! == a || I[l]! == b || I[l]! == c || I[l]! == ab || I[l]! == ac || I[l]! == bc ||
        I[l]! == abc)

@[expose] def thirdOK (I : Array Tab) (C : Array (Array Bool)) (i j : Nat) : Bool :=
  let ab := comp 32 I[i]! I[j]!
  allBelow I.size fun k =>
    !((C[i]!)[k]! && (C[j]!)[k]!) || k == i || k == j || I[k]! == ab || fourthOK I C i j k

@[expose] def noE16Check (_ : Unit := ()) : Bool :=
  let I := invTabs ()
  let C := commMat I
  allBelow I.size fun i => allBelow I.size fun j => !((C[i]!)[j]!) || i == j || thirdOK I C i j

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
