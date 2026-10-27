module

public import Certificates.Data.Kernel.ReflExt.ReflExtK

public section

namespace CFSG.ReflExt.NK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.PosBK
  CFSG.ReflExt.RXK

abbrev Rep0 := (Nat × Nat) × WitK.Rec

abbrev Rep1 := (Nat × Nat) × Nat × WitK.Rec × List (Nat × Nat × Nat × Nat) × List Rep0 ×
  List (Nat × Nat × List Nat)

abbrev FDN := List (Nat × Nat × Nat × Nat) × List (Nat × List Nat × List Nat) ×
  List (Nat × Nat) × List (List Nat) × List Rep0 × List Rep1

@[expose] def rec0 : WitK.Rec := (0, [], [], [], [])

@[expose] def r00 : Rep0 := ((0, 0), rec0)

@[expose] def r10 : Rep1 := ((0, 0), 0, rec0, [], [], [])

@[expose] noncomputable def takeK {α : Type} (l : List α) : Nat → List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun x _ ih k => Nat.rec (motive := fun _ => List α) [] (fun k' _ => x :: ih k') k) l

@[expose] noncomputable def slc {α : Type} (s k : Nat) (l : List α) : List α :=
  takeK (dropK (Nat.mul k s) l) s

@[expose] noncomputable def upk (D : Nat) : Nat → Vec :=
  Nat.rec (motive := fun _ => Nat → Vec) (fun _ => [])
    (fun _ ih n => Nat.mod n 65536 :: ih (Nat.div n 65536)) D

@[expose] noncomputable def ptX (P : Pt) (ex : List (Nat × Nat)) (b : Nat) : Pt :=
  { P with gens := P.gens ++ ex.map (fun r => (⟨(upk P.D r.2).reverse, upk P.D r.1⟩ : Refl)),
           bound := b }

@[expose] noncomputable def recBad (Q : Pt) (r : WitK.Rec) : Bool :=
  (Nat.beq r.1 1 || Nat.beq r.1 2) && chkPt Q r

@[expose] noncomputable def bkS (N : Nat) (bk : List (Nat × List Nat × List Nat)) :
    Nat → Nat × Nat × Bool → Nat × Nat × Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat × Nat × Bool → Nat × Nat × Bool → Bool)
    (fun _ sf sh => sf.2.2 && sh.2.2 && Nat.beq sf.2.1 N && Nat.beq sh.2.1 N)
    (fun b _ ih prev sf sh =>
      Nat.ble prev b.1 && ih (Nat.succ b.1) (addC N b.2.1 sf) (addC N b.2.2 sh)) bk

@[expose] noncomputable def mskB (F : Fd) (D : Nat) (R : List (Nat × Nat))
    (bk : List (Nat × List Nat × List Nat)) : Bool :=
  allK (fun b => allK (fun k => Nat.beq (mskF F R (pkrC D k)) b.1) b.2.1 &&
    allK (fun k => Nat.beq (mskH F R (pkC D k)) b.1) b.2.2) bk

@[expose] noncomputable def cloE (G : List (Nat × Nat)) (rows : List (Nat × Nat × Nat × Nat)) :
    List (Nat × Nat) :=
  G ++ rows.map fun e => (e.2.2.1, e.2.2.2)

@[expose] noncomputable def tagN (F : Fd) (D n nC X : Nat) (G C : List (Nat × Nat))
    (R0 : List Rep0) (R1 : List Rep1) (c : Nat × Nat) (t : List Nat) : Bool :=
  let fx := Nat.beq (dotK F c.2 X) 0
  List.rec (motive := fun _ => Bool) false
    (fun ty r _ => List.rec (motive := fun _ => Bool) false
      (fun j u _ =>
        bif Nat.beq ty 0 then fx && u.isEmpty && Nat.blt j nC && eqPM F D c (nthK (0, 0) C j)
        else bif Nat.beq ty 1 then
          fx && Nat.blt j R0.length && ltAll n u && eqPM F D (nthK r00 R0 j).1 (cw F G u c)
        else Nat.beq ty 2 && !fx && Nat.blt j R1.length && ltAll n u &&
          eqPM F D (nthK r10 R1 j).1 (cw F G u c)) r) t

@[expose] noncomputable def centK (F : Fd) (D : Nat) (G : List (Nat × Nat)) (r : Nat × Nat) : Bool :=
  allK (fun g => Nat.rec (motive := fun _ => Bool) true
    (fun j ih =>
      let e := Nat.shiftLeft 1 (Nat.mul 16 j)
      Nat.beq (appK F g (appK F r e)) (appK F r (appK F g e)) && ih) D) G

@[expose] noncomputable def tag2N (F : Fd) (D n1 nC2 X : Nat) (G1 C2 : List (Nat × Nat))
    (Q : List Rep0) (c : Nat × Nat) (t : Nat × Nat × List Nat) : Bool :=
  let k := t.2.1
  bif Nat.beq t.1 0 then Nat.blt k nC2 && eqPM F D c (nthK (0, 0) C2 k)
  else bif Nat.beq t.1 1 then
    Nat.blt k nC2 &&
      (let ρ := nthK (0, 0) C2 k
       bne (Nat.beq (dotK F c.2 ρ.1) 0) (Nat.beq (dotK F ρ.2 c.1) 0))
  else bif Nat.beq t.1 2 then
    Nat.blt k Q.length && ltAll n1 t.2.2 && eqPM F D (nthK r00 Q k).1 (cw F G1 t.2.2 c)
  else Nat.beq t.1 3 && Nat.beq (dotK F c.2 X) 0

@[expose] noncomputable def needs2 (rp : Rep1) : Bool := Nat.beq rp.2.1 0 || Nat.beq rp.2.2.1.1 3

@[expose] noncomputable def s2N (P : Pt) (F : Fd) (G : List (Nat × Nat)) (X : Nat)
    (cd : List (Nat × Nat)) (rp : Rep1) : Bool :=
  let G1 := G ++ [rp.1]
  let n1 := G1.length
  let ro := rp.2.2.2.1
  let C2 := cloE G1 ro
  let Q := rp.2.2.2.2.1
  cloP F n1 G1 ro n1 0 C2 &&
    (bif Nat.beq rp.2.1 0 then allK (fun e => eqPM F P.D e rp.1 || Nat.beq (dotK F e.2 X) 0) C2
     else true) &&
    allK (fun q => reflOK F q.1 && recBad (ptX P [rp.1, q.1] P.bound) q.2) Q &&
    all2 (tag2N F P.D n1 (Nat.add n1 ro.length) X G1 C2 Q) cd rp.2.2.2.2.2

@[expose] noncomputable def allI {α : Type} (f : Nat → α → Bool) (l : List α) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih j => f j x && ih (Nat.succ j))
    l i

@[expose] noncomputable def partN (P : Pt) (B : Nat) (d : FDN) (i : Nat) : Bool :=
  let F := ptF P
  let G := gensK P
  let n := G.length
  let C := cloE G d.1
  let X := pk P.D P.x
  bif Nat.beq i 0 then
    Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 9 && allK (reflOK F) G &&
      allK (fun g => Nat.beq (dotK F g.2 X) 0) G && cloP F n G d.1 n 0 C &&
      allK (fun r => Nat.beq (dotK F r.2 X) 0) C &&
      bkS (Nat.pow 3 P.D) d.2.1 0 (0, 0, true) (0, 0, true)
  else bif Nat.blt i 9 then
    mskB F P.D C (slc (Nat.succ (Nat.div d.2.1.length 8)) (Nat.sub i 1) d.2.1)
  else bif Nat.beq i 9 then candOK F P.D d.2.1 d.2.2.1
  else bif Nat.blt i 14 then
    let s := Nat.succ (Nat.div d.2.2.1.length 4)
    all2 (tagN F P.D n (Nat.add n d.1.length) X G C d.2.2.2.2.1 d.2.2.2.2.2)
      (slc s (Nat.sub i 10) d.2.2.1) (slc s (Nat.sub i 10) d.2.2.2.1)
  else bif Nat.beq i 14 then
    allK (fun rp => reflOK F rp.1 && Nat.beq (dotK F rp.1.2 X) 0 && recBad (ptX P [rp.1] B) rp.2)
      d.2.2.2.2.1
  else bif Nat.beq i 15 then
    allK (fun rp => reflOK F rp.1 && !(Nat.beq (dotK F rp.1.2 X) 0) &&
      (bif Nat.beq rp.2.1 0 then centK F P.D G rp.1
       else (Nat.beq rp.2.2.1.1 1 || Nat.beq rp.2.2.1.1 2 || Nat.beq rp.2.2.1.1 3) &&
         chkPt (ptX P [rp.1] P.bound) rp.2.2.1)) d.2.2.2.2.2
  else Nat.blt i 20 &&
    allI (fun j rp => bne (Nat.beq (Nat.mod j 4) (Nat.sub i 16)) true || !(needs2 rp) ||
      s2N P F G X d.2.2.1 rp) d.2.2.2.2.2 0

end CFSG.ReflExt.NK

end
