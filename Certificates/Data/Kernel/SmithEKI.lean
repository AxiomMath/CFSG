module

public import Certificates.Data.Kernel.SmithEKS
public import Certificates.Data.Kernel.SmithEKW

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

@[expose] def basL (L : List Nat) : List Nat := ((gensL L).foldl insertVec []).map (·.2)

@[expose] def basRow (T : List (List (List (List Nat)))) (p : Nat) (B : List Nat) : Bool :=
  basL (tvW T p) == B && B.length == 6 && B.all (fun b => decide (b < 2 ^ 20))

@[expose] noncomputable def basOK (T : List (List (List (List Nat)))) :
    List Nat → List (List Nat) → Bool :=
  fun P => List.rec (motive := fun _ => List (List Nat) → Bool) (fun Bs => Bs.isEmpty)
    (fun p _ ih Bs => basRow T p (Bs.headD []) && ih Bs.tail) P

@[expose] noncomputable def spanL : List Nat → List Nat :=
  fun B => List.rec (motive := fun _ => List Nat) [0]
    (fun b _ ih => ih ++ ih.map (b ^^^ ·)) B

@[expose] noncomputable def spanM (B : List Nat) : Nat := CFSG.SmithL6.K.maskOf (spanL B)

@[expose] def pairI (W1 p m q m' : Nat) : Bool :=
  let I := m &&& m'
  I == 1 || (hermC p q == 0 && I &&& W1 == I)

@[expose] noncomputable def rowI (W1 p m : Nat) : List Nat → List Nat → Bool :=
  fun P => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun q _ ih Ms => pairI W1 p m q (Ms.headD 0) && ih Ms.tail) P

@[expose] noncomputable def rowsI (W1 : Nat) :
    List Nat → List Nat → List Nat → List Nat → Bool :=
  fun R => List.rec (motive := fun _ => List Nat → List Nat → List Nat → Bool) (fun _ _ _ => true)
    (fun p _ ih S Pt Mt => rowI W1 p (S.headD 0) Pt Mt && ih S.tail Pt.tail Mt.tail) R

@[expose] noncomputable def chunkI (W1 : Nat) (P Ms : List Nat) (a n : Nat) : Bool :=
  rowsI W1 ((P.drop a).take n) ((Ms.drop a).take n) (P.drop (a + 1)) (Ms.drop (a + 1))

end CFSG.SmithE.K
