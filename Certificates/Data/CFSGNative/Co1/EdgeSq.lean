module

public import Certificates.Data.CFSGNative.Co1.S365CentRoot

public section

namespace CFSG.Sporadic.Co1.EdgeSqNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native
  CFSG.Sporadic.Co1.S365UNative

@[expose] def bil0N (f0t : Array Nat) (u v : Nat) : Bool := parity24N (u &&& vecMulN 24 f0t v)

@[expose] def kerList (Mt : Array Nat) : List Nat :=
  ((List.range 24).foldl (fun (st : List (Nat × Nat) × List Nat) j =>
    let r := reduceBy st.1 (onePlus Mt (1 <<< j)) (1 <<< j)
    if r.1 == 0 then (st.1, r.2 :: st.2)
    else (insertBasis st.1 (onePlus Mt (1 <<< j)) (1 <<< j), st.2)) ([], [])).2

@[expose] def fixedIdx (pts : Array Nat) (n : Nat) (Mt : Array Nat) : List Nat :=
  (List.range n).filter fun p => isFixedN Mt pts[p]!

@[expose] def pairOKN (qr f0t pts : Array Nat) (pos : Array UInt32) (n : Nat) (X : List Nat)
    (B : List (Nat × Nat)) (Mt : Array Nat) (a b : Nat) : Bool :=
  !(tyLabN qr pts pos n (a ^^^ b) == 3) || X.any (fun x => bil0N f0t a x) ||
    (match memPre B b with
      | some y => onePlus Mt y == b && bil0N f0t a y
      | none => false)

@[expose] def edgeCheckN (qr f0t pts : Array Nat) (pos : Array UInt32) (n : Nat)
    (S : Array Nat) : Bool :=
  let Mt := transposeRows 24 S
  let B := imBasis Mt
  let X := kerList Mt
  let F := fixedIdx pts n Mt
  X.all (fun x => decide (x < 2 ^ 24) && isFixedN Mt x) &&
    F.all fun p => F.all fun p' => pairOKN qr f0t pts pos n X B Mt pts[p]! pts[p']!

end CFSG.Sporadic.Co1.EdgeSqNative
