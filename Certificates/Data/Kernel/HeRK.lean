module

public import Certificates.Data.Kernel.HexaK
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.HeRK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def letC (G GI : Nat → Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (GI (Nat.mod (Nat.div c 2) 8)) (G (Nat.mod (Nat.div c 2) 8))
    (Nat.beq (Nat.mod c 2) 0)

@[expose] noncomputable def codeK (G GI : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 8330 14)
    (fun c _ acc => strictN acc fun acc => mul 8330 14 (letC G GI c) acc) w

@[expose] noncomputable def codeInv (w : List Nat) : List Nat := (w.map fun c => Nat.xor c 1).reverse

@[expose] noncomputable def fixK (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i s => nIf(Nat.beq (pg 14 (mask 14) p i) i, Nat.succ s, s)) 8330

@[expose] noncomputable def invol346 (p : Nat) : Bool :=
  andB (Nat.beq (mul 8330 14 p p) (pidn 8330 14))
    (andB (notB (Nat.beq p (pidn 8330 14))) (Nat.beq (fixK p) 346))

@[expose] noncomputable def commP (a ai b bi : Nat) : Nat :=
  mul 8330 14 a (mul 8330 14 b (mul 8330 14 ai bi))

@[expose] noncomputable def heRK1 (G GI : Nat → Nat) (rw : List (List Nat)) (yw : List Nat) : Bool :=
  strictB (codeK G GI (rw.getD 0 [])) fun r1 => strictB (codeK G GI (rw.getD 1 [])) fun r2 =>
  strictB (mul 8330 14 r1 r2) fun r3 => strictB (codeK G GI yw) fun y =>
  andB (invol346 r1) (andB (invol346 r2)
  (andB (Nat.beq (mul 8330 14 r1 r2) (mul 8330 14 r2 r1)) (andB (invol346 r3)
  (andB (Nat.beq (mul 8330 14 y r1) (mul 8330 14 r1 y))
  (notB (Nat.beq (mul 8330 14 y r2) (mul 8330 14 r2 y)))))))

@[expose] noncomputable def heRK2 (G GI : Nat → Nat) (rw cw : List (List Nat)) (k : Nat) : Bool :=
  strictB (codeK G GI (rw.getD 0 [])) fun r1 => strictB (codeK G GI (rw.getD 1 [])) fun r2 =>
  strictB (codeK G GI (cw.getD k [])) fun u =>
  andB (permOK 8330 14 (mask 14) (8330 * 14) u (codeK G GI (codeInv (cw.getD k []))))
    (andB (Nat.beq (mul 8330 14 u r1) (mul 8330 14 r1 u))
      (Nat.beq (mul 8330 14 u r2) (mul 8330 14 r2 u)))

@[expose] noncomputable def heRK3 (G GI PS : Nat → Nat) (cw : List (List Nat)) (j : Nat) : Bool :=
  Nat.beq (PS j)
    (commP (codeK G GI (cw.getD (2 * j) [])) (codeK G GI (codeInv (cw.getD (2 * j) [])))
      (codeK G GI (cw.getD (2 * j + 1) [])) (codeK G GI (codeInv (cw.getD (2 * j + 1) []))))

@[expose] noncomputable def heRK4 (PS PSI : Nat → Nat) (D : Nat → List Int) : Bool :=
  andB (allN 9 fun j => permOK 8330 14 (mask 14) (8330 * 14) (PS j) (PSI j))
    (allN 7 fun j => wordEqK 8330 14 (mask 14) (pidn 8330 14) PS PSI (2 + j) (D (2 + j))
      (PS (2 + j)))

end CFSG.KC.HeRK

end
