module

public import Certificates.Data.Kernel.LyBenes.Check
public import Certificates.Data.Kernel.LyGlue.Defs

public section

namespace CFSG.KC.LyBase

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.LyGlue CFSG.KC.LyBenes
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def lIf (c : Bool) (t e : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) e t c

@[expose] noncomputable def jC (j : Nat) : List Nat :=
  lIf (Nat.beq j 0) [0] (lIf (Nat.beq j 1) [2] (lIf (Nat.beq j 2) [3]
    (lIf (Nat.beq j 3) [2, 0, 2, 2, 0, 3, 3, 1, 3]
      (lIf (Nat.beq j 4) [2, 2, 0, 2, 0, 3, 1, 3, 3]
        (lIf (Nat.beq j 5) [2, 0, 2, 0, 2, 2, 0, 3, 3, 1, 3, 1, 3] [])))))

@[expose] noncomputable def cdPtC (cF dF : Nat → Nat) (cs : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) a (fun x _ ih => strictN ih fun b => letE cF dF x b) cs

@[expose] noncomputable def jwPt (cF dF : Nat → Nat) (w : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) a (fun j _ ih => strictN ih fun b => cdPtC cF dF (jC j) b) w

@[expose] noncomputable def fixAll (cF dF : Nat → Nat) (bs w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (Nat.beq (jwPt cF dF w b) b) ih) bs

@[expose] noncomputable def bFix (cF dF : Nat → Nat) (bs : List Nat) (r : List (Fin 6 × Bool)) :
    Bool :=
  andB (isBWord r) (fixAll cF dF bs (r.map letIdx))

@[expose] noncomputable def closeStep (Ws : List (List Nat)) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) X
    (fun Ns _ ih => strictN ih fun Y => Nat.lor Y (netsApply 17 131072 1 Ns X)) Ws

@[expose] noncomputable def closeR (Ws : List (List Nat)) (r X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ ih => strictN ih fun Y => closeStep Ws Y) r

@[expose] noncomputable def popMask (W i : Nat) : Nat :=
  Nat.mul (Nat.div (ones W) (ones (Nat.shiftLeft 2 i))) (ones (Nat.shiftLeft 1 i))

@[expose] noncomputable def popc (k X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land X (ones (Nat.shiftLeft 1 k)))
    (fun i acc => strictN acc fun y =>
      Nat.add (Nat.land y (popMask (Nat.shiftLeft 1 k) i))
        (Nat.land (Nat.shiftRight y (Nat.shiftLeft 1 i)) (popMask (Nat.shiftLeft 1 k) i))) k

@[expose] noncomputable def orbitOK (Ws : List (List Nat)) (r β m : Nat) : Bool :=
  Nat.ble m (popc 17 (closeR Ws r (Nat.shiftLeft 1 β)))

@[expose] noncomputable def distinctN (O : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih' => andB (notB (Nat.beq x y)) ih') xs) ih) O

@[expose] noncomputable def edgeOK (cF dF : Nat → Nat) (Ws : List (List Nat)) (O : List Nat)
    (T : List (Nat × Nat)) (i : Nat) : Bool :=
  andB (Nat.ble (T.getD i (0, 0)).1 i)
    (Nat.beq (jwPt cF dF (Ws.getD (T.getD i (0, 0)).2 []) (O.getD (T.getD i (0, 0)).1 0))
      (O.getD (Nat.succ i) 0))

@[expose] noncomputable def treeOK (cF dF : Nat → Nat) (Ws : List (List Nat)) (β m : Nat)
    (O : List Nat) (T : List (Nat × Nat)) : Bool :=
  andB (andB (distinctN O) (Nat.ble m O.length))
    (andB (andB (Nat.beq (O.getD 0 0) β) (Nat.beq O.length (Nat.succ T.length)))
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => andB ih (edgeOK cF dF Ws O T i)) T.length))

end CFSG.KC.LyBase

end
