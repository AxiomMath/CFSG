module

public import Certificates.Data.Kernel.E64F

public section

namespace CFSG.KC.SLOrb

open CFSG.KC.E64F

@[expose] def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.blt a b || (Nat.beq a b && lexLt as bs)

@[expose] def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && eqL as bs
  | _, _ => false

@[expose] def mergeU : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | 0, A, B => A ++ B
  | _ + 1, [], B => B
  | _ + 1, A, [] => A
  | f + 1, a :: A, b :: B =>
    if eqL a b then a :: mergeU f A B
    else if lexLt a b then a :: mergeU f A (b :: B) else b :: mergeU f (a :: A) B

@[expose] def mergePairs : List (List (List Nat)) → List (List (List Nat))
  | A :: B :: R => mergeU (A.length + B.length) A B :: mergePairs R
  | R => R

@[expose] def mergeAll : Nat → List (List (List Nat)) → List (List Nat)
  | _, [] => []
  | _, [A] => A
  | 0, R => R.flatten
  | f + 1, R => mergeAll f (mergePairs R)

@[expose] def msortU (A : List (List Nat)) : List (List Nat) :=
  mergeAll 64 (A.map fun x => [x])

@[expose] def subS : Nat → List (List Nat) → List (List Nat) → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | 0, _, _ => false
  | f + 1, a :: A, b :: B =>
    if eqL a b then subS f A B else if lexLt b a then subS f (a :: A) B else false

@[expose] def subL (A B : List (List Nat)) : Bool := subS (A.length + B.length + 1) A B

@[expose] def sortedB : List (List Nat) → Bool
  | a :: b :: R => lexLt a b && sortedB (b :: R)
  | _ => true

@[expose] def imgs (actF : Nat → List Nat → List Nat) (m : Nat) (A : List (List Nat)) :
    List (List Nat) :=
  A.flatMap fun x => (List.range m).map fun l => actF l x

@[expose] def diffS : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | _, [], _ => []
  | _, I, [] => I
  | 0, _, _ => []
  | f + 1, a :: I, b :: S =>
    if eqL a b then diffS f I S
    else if lexLt a b then a :: diffS f I (b :: S) else diffS f (a :: I) S

@[expose] def layers (actF : Nat → List Nat → List Nat) (m : Nat) :
    Nat → List (List Nat) → List (List Nat) → List (List (List Nat))
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | f + 1, S, F =>
    let I := msortU (imgs actF m F)
    let N := diffS (I.length + S.length) I S
    F :: layers actF m f (mergeU (S.length + N.length) S N) N

@[expose] def chainOK (actF : Nat → List Nat → List Nat) (m : Nat) :
    List (List (List Nat)) → Bool
  | A :: B :: R => subL B (msortU (imgs actF m A)) && chainOK actF m (B :: R)
  | _ => true

@[expose] def orbChk (actF : Nat → List Nat → List Nat) (m : Nat) (Δ : List Nat) (s : Nat) :
    Bool :=
  let Ls := layers actF m (s + 1) [Δ] [Δ]
  let O := msortU Ls.flatten
  (match Ls with | F :: _ => subL F [Δ] | [] => false) && chainOK actF m Ls && sortedB O &&
    O.length == s && subL [Δ] O && subL (msortU (imgs actF m O)) O

@[expose] def goodB (n : Nat) (t : Array Nat) (f : Nat → Nat) : Bool :=
  t.size == n && (List.range n).all fun p => t.getD p 0 == f p && Nat.blt (f p) n

@[expose] def ltB (n : Nat) (t : Array Nat) : Bool :=
  (List.range n).all fun p => Nat.blt (t.getD p 0) n

end CFSG.KC.SLOrb

end
