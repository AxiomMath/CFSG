module

public import Certificates.Data.Kernel.SmithEKO

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73 CFSG.KC.Misc CFSG.KC.LQT.P

@[expose] noncomputable def ivOn (CP S2 x y z : Nat) : Bool :=
  !Nat.beq x y && !Nat.beq y z && !Nat.beq x z &&
    bitK S2 (Nat.xor (Nat.xor (at' 9 CP x) (at' 9 CP y)) (at' 9 CP z))

@[expose] noncomputable def ivP (CP S2 z a b : Nat) : Bool :=
  Nat.beq z a || Nat.beq z b || ivOn CP S2 z a b

@[expose] noncomputable def ivLn (LI LM a b : Nat) : Nat :=
  at' 21 LM (at' 6 LI (Nat.add (Nat.mul 21 a) b))

@[expose] noncomputable def ivLm (CP S2 LI LM : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun a acc => acc &&
    Nat.rec (motive := fun _ => Bool) true (fun b acc2 => acc2 &&
      Nat.blt (at' 6 LI (Nat.add (Nat.mul 21 a) b)) 42 &&
      Nat.rec (motive := fun _ => Bool) true (fun z acc3 => acc3 &&
        (bitK (ivLn LI LM a b) z == ivP CP S2 z a b)) 21) 21) 21

@[expose] noncomputable def ivLow (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => bif bitK m (Nat.sub 20 k) then Nat.sub 20 k
    else acc) 21

@[expose] noncomputable def ivMp (LM MP : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => acc &&
    Nat.rec (motive := fun _ => Bool) true (fun j acc2 => acc2 &&
      Nat.beq (at' 5 MP (Nat.add (Nat.mul 42 i) j)) (ivLow (Nat.land (at' 21 LM i) (at' 21 LM j))))
      42) 42

@[expose] noncomputable def ivMeet (LI MP a b c d : Nat) : Nat :=
  at' 5 MP (Nat.add (Nat.mul 42 (at' 6 LI (Nat.add (Nat.mul 21 a) b)))
    (at' 6 LI (Nat.add (Nat.mul 21 c) d)))

@[expose] noncomputable def ivPack : List Nat → Nat :=
  fun l => List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.mul 32 ih)) l

@[expose] noncomputable def ivList (LI MP y0 y1 y2 y3 y4 : Nat) : List Nat :=
  let x2 := ivMeet LI MP y0 y1 y2 y3
  let x5 := ivMeet LI MP y0 y2 y1 y3
  let x6 := ivMeet LI MP y0 y3 y1 y2
  let x7 := ivMeet LI MP y1 y3 y2 y4
  let x8 := ivMeet LI MP y0 y2 y4 x6
  let x9 := ivMeet LI MP y0 y1 y3 x8
  let x11 := ivMeet LI MP y1 y3 y2 x9
  let x16 := ivMeet LI MP y0 y2 y3 y4
  [y0, y1, x2, y4, y2, x5, x6, x7, x8, x9, y3, x11, ivMeet LI MP y0 x11 y1 y2,
    ivMeet LI MP y0 x11 y1 x8, ivMeet LI MP y0 y3 y1 x8, ivMeet LI MP y0 x7 y1 x8, x16,
    ivMeet LI MP y0 x7 y1 y2, ivMeet LI MP y0 x7 y1 x16, ivMeet LI MP y0 x11 y1 x16,
    ivMeet LI MP y0 y3 y1 x16]

@[expose] noncomputable def ivGet : List Nat → Nat → Nat :=
  fun l => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) l

@[expose] noncomputable def ivBack (l : List Nat) : Bool :=
  Nat.beq (ivGet l (ivGet l 0)) 0 && Nat.beq (ivGet l (ivGet l 1)) 1 &&
    Nat.beq (ivGet l (ivGet l 4)) 4 && Nat.beq (ivGet l (ivGet l 10)) 10 &&
    Nat.beq (ivGet l (ivGet l 3)) 3

@[expose] noncomputable def ivAmat (CP s a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (bif bitK a j then at' 9 CP (at' 5 s j) else 0)) 9

@[expose] noncomputable def ivInv (CP s : Nat) : Bool :=
  letB s fun s =>
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => acc && Nat.beq (at' 5 s (at' 5 s k)) k) 21 &&
  !Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && Nat.beq (at' 5 s k) k) 21 &&
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && Nat.blt (at' 5 s k) 21) 21 &&
  Nat.beq (Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (at' 5 s k))) 21) 2097151 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => acc && Nat.beq (ivAmat CP s (at' 9 CP k)) (at' 9 CP (at' 5 s k))) 21

@[expose] noncomputable def ivBits (m : Nat) (f : Nat → List Nat → List Nat) (t : List Nat) :
    List Nat :=
  letLN m fun m => Nat.rec (motive := fun _ => List Nat → List Nat) (fun t => t)
    (fun k ih t => ih (bif bitK m k then f k t else t)) 21 t

@[expose] noncomputable def ivAll : Nat := 2097151

@[expose] noncomputable def ivGrp (CP LI LM MP y0 : Nat) (t : List Nat) : List Nat :=
  ivBits (Nat.xor ivAll (Nat.shiftLeft 1 y0)) (fun y1 t =>
    letLN (ivLn LI LM y0 y1) fun L01 =>
    ivBits (Nat.xor ivAll L01) (fun y2 t =>
      ivBits (Nat.xor ivAll (Nat.lor L01 (Nat.lor (ivLn LI LM y0 y2) (ivLn LI LM y1 y2))))
        (fun y3 t =>
        ivBits (Nat.land (Nat.xor L01 (Nat.lor (Nat.shiftLeft 1 y0) (Nat.shiftLeft 1 y1)))
            (Nat.xor ivAll (ivLn LI LM y2 y3))) (fun y4 t =>
          (fun l => bif ivBack l then (letLN (ivPack l) fun s => bif ivInv CP s then s :: t else t)
            else t) (ivList LI MP y0 y1 y2 y3 y4)) t) t) t) t

end CFSG.SmithE.K
