module

public import Certificates.Data.Kernel.SmithEKO

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def cdCo (c i : Nat) : Nat := Nat.land (Nat.shiftRight c (Nat.mul 2 i)) 3

@[expose] noncomputable def cdMul (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mul (Nat.mod x 2) (Nat.mod y 2)) (Nat.mul (Nat.div x 2) (Nat.div y 2))) 2)
    (Nat.mul 2 (Nat.mod (Nat.add (Nat.add (Nat.mul (Nat.mod x 2) (Nat.div y 2))
      (Nat.mul (Nat.div x 2) (Nat.mod y 2))) (Nat.mul (Nat.div x 2) (Nat.div y 2))) 2))

@[expose] noncomputable def cdMapC (g : Nat → Nat → Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.mul (g i (cdCo c i)) (Nat.pow 4 i))) 6

@[expose] noncomputable def cdFrob (c : Nat) : Nat := cdMapC (fun _ x => cdMul x x) c

@[expose] noncomputable def cdDlt (c : Nat) : Nat :=
  cdMapC (fun i x => bif Nat.blt i 2 then cdMul 2 x else x) c

@[expose] noncomputable def cdLead (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun n acc => bif Nat.beq (cdCo c (Nat.sub 5 n)) 0 then acc else cdCo c (Nat.sub 5 n)) 6

@[expose] noncomputable def cdNorm (c : Nat) : Nat :=
  cdMapC (fun _ x => cdMul (cdMul (cdLead c) (cdLead c)) x) c

@[expose] noncomputable def cdFB (u v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => xor acc (xor (bitK u (Nat.mul 2 k) && bitK v (Nat.add (Nat.mul 2 k) 1))
      (bitK u (Nat.add (Nat.mul 2 k) 1) && bitK v (Nat.mul 2 k)))) 10

@[expose] noncomputable def cdSel (bs : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih k => Nat.xor (bif bitK m k then b else 0) (ih (Nat.succ k))) bs 0

@[expose] noncomputable def cdIndK (bs : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m acc => acc && !Nat.beq (Nat.mod (cdSel bs (Nat.succ m)) (Nat.pow 2 20)) 0)
    (Nat.sub (Nat.pow 2 (lenK bs)) 1)

@[expose] noncomputable def cdImg (TP : Nat → Nat) (W : List Nat) (L a : Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun n ih y => ih (bif bitK a n then at' 10 (TP (W.getD n 0)) y else y)) 9 (at' 10 L x)

@[expose] noncomputable def cdRedK (TP : Nat → Nat) (W : List Nat) (L : Nat) (C S R : List Nat)
    (a e : Nat) : Bool :=
  bif bitK e 0 then
    (Nat.blt (Nat.div e 2) 693 &&
      !Nat.beq (cdImg TP W L a (cdImg TP W L a (Nat.div e 2))) (Nat.div e 2))
  else
    (Nat.blt (Nat.mod (Nat.div e 2) 512) 512 &&
      memK (Nat.xor (Nat.xor a (Nat.mod (Nat.div e 2) 512)) (amK C S (Nat.mod (Nat.div e 2) 512)))
        R &&
      Nat.beq (Nat.xor (Nat.xor a (Nat.mod (Nat.div e 2) 512)) (amK C S (Nat.mod (Nat.div e 2) 512)))
        (Nat.div (Nat.div e 2) 512))

@[expose] noncomputable def cdRedAll (TP : Nat → Nat) (W : List Nat) (L : Nat) (C S R : List Nat) :
    List Nat → Nat → Bool :=
  fun RD => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih a => cdRedK TP W L C S R a e && ih (Nat.succ a)) RD

@[expose] noncomputable def cdPlK (TP : Nat → Nat) (W : List Nat) (L a : Nat) (PL : List (List Nat))
    (PM : List Nat) (i i' : Nat) : Bool :=
  Nat.blt i 891 && Nat.blt i' 891 &&
    (PL.getD i []).all fun x => bitK (PM.getD i' 0) (cdImg TP W L a x)

@[expose] noncomputable def cdVecs (WT : List Nat) : List Nat → List Nat
  | i :: i' :: r => Nat.xor (WT.getD i' 0) (WT.getD i 0) :: cdVecs WT r
  | _ => []

@[expose] noncomputable def cdPairs (TP : Nat → Nat) (W : List Nat) (L a : Nat)
    (PL : List (List Nat)) (PM : List Nat) : List Nat → Bool
  | i :: i' :: r => cdPlK TP W L a PL PM i i' && cdPairs TP W L a PL PM r
  | [] => true
  | _ => false

@[expose] noncomputable def cdRepK (TP : Nat → Nat) (W LT : List Nat) (PL : List (List Nat))
    (PM WT : List Nat) (r : List Nat) : Bool :=
  let j := r.getD 0 0
  let a := r.getD 1 0
  let t := r.getD 2 0
  let e₁ := r.getD 3 0
  let e₂ := r.getD 4 0
  let L := LT.getD j 0
  let ps := r.drop 5
  Nat.beq (lenK ps) 10 && cdPairs TP W L a PL PM ps && cdIndK (cdVecs WT ps) &&
    (bif Nat.beq t 0 then cdPlK TP W L a PL PM e₁ e₂ && cdFB (WT.getD e₂ 0) (WT.getD e₁ 0)
     else bif Nat.beq t 1 then
       Nat.blt e₁ 891 && (PL.getD e₁ []).all fun x => Nat.beq (cdImg TP W L a x) x
     else Nat.beq t 2)

@[expose] noncomputable def cdInvK (As : List Nat) (B : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x acc => acc && Nat.blt (at' 10 B x) 693 &&
      Nat.beq (As.foldr (fun A y => at' 10 A y) (at' 10 B x)) x) 693

@[expose] noncomputable def cdMapK (f : Nat → Nat) (PC : List Nat) (T : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun p acc => acc && Nat.blt (at' 10 T p) 693 &&
      Nat.beq (PC.getD (at' 10 T p) 0) (cdNorm (f (PC.getD p 0)))) 693

@[expose] noncomputable def cdCompK (L : Nat) (As : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x acc => acc && Nat.beq (at' 10 L x) (As.foldr (fun A y => at' 10 A y) x)) 693

@[expose] noncomputable def cdSaK (W : List Nat) (L : Nat) (S : List Nat) : Bool :=
  Nat.beq (lenK S) 21 && ltK 21 S &&
    Nat.rec (motive := fun _ => Bool) true
      (fun k acc => acc && Nat.beq (W.getD (S.getD k 0) 0) (at' 10 L (W.getD k 0))) 21

end CFSG.SmithE.K
