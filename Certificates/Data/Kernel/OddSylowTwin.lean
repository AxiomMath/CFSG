module

public section

namespace CFSG.KD.OddSyl

@[expose] def ilMul (f g : List Nat) : List Nat := g.map fun y => f.getD y 0

@[expose] def ilLetter (n : Nat) (L Li : List (List Nat)) : Int → List Nat
  | Int.ofNat 0 => Li.getD 0 (List.range n)
  | Int.ofNat (k + 1) => L.getD k (List.range n)
  | Int.negSucc k => Li.getD k (List.range n)

@[expose] def evW (n : Nat) (L Li : List (List Nat)) : List Int → List Nat
  | [] => List.range n
  | z :: w => ilMul (ilLetter n L Li z) (evW n L Li w)

@[expose] def ilPow (n : Nat) (x : List Nat) : Nat → List Nat
  | 0 => List.range n
  | k + 1 => ilMul x (ilPow n x k)

@[expose] def fixL (l : List Nat) : Nat := (List.range l.length).countP fun i => l.getD i 0 == i

@[expose] def nodupB : List (List Nat) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupB xs

@[expose] def witOK (n : Nat) (L Li : List (List Nat)) (reps : List (List Int))
    (t : List Int × List Int × Nat) : Bool :=
  Nat.blt t.2.2 reps.length &&
    ilMul (evW n L Li t.1) (evW n L Li t.2.1) == ilMul (evW n L Li t.2.1)
      (evW n L Li (reps.getD t.2.2 []))

@[expose] def subOK (n : Nat) (V : List (List Nat)) (p card : Nat) : Bool :=
  nodupB V && V.length == card && V.all (fun x => V.all fun y => V.contains (ilMul x y)) &&
    V.all fun x => ilPow n x p == List.range n

@[expose] def sylOK (n : Nat) (L Li : List (List Nat)) (reps : List (List Int)) (p card : Nat)
    (W : List (List Int × List Int × Nat)) : Bool :=
  subOK n (([] :: W.map (·.1)).map (evW n L Li)) p card && W.all (witOK n L Li reps)

@[expose] def repOK (n : Nat) (L Li : List (List Nat)) (w : List Int) (m f : Nat) : Bool :=
  ilPow n (evW n L Li w) m == List.range n && !(evW n L Li w == List.range n) &&
    fixL (evW n L Li w) == f

end CFSG.KD.OddSyl

end
