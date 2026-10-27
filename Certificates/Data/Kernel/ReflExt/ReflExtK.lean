module

public import Certificates.Data.Kernel.TwoNodeSmall.PosBK

public section

namespace CFSG.ReflExt.RXK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.PosBK

abbrev Rep := (Nat × Nat) × ORec × Nat × List (Nat × Nat × Nat × Nat) ×
  List ((Nat × Nat) × ORec) × List (Nat × Nat × List Nat)

abbrev FD := List (Nat × Nat × Nat × Nat) × List (Nat × List Nat × List Nat) × List (Nat × Nat) ×
  List (List Nat) × List Rep

@[expose] def rep0 : Rep := ((0, 0), ([], 0, 0, [], [], [], []), 0, [], [], [])

@[expose] noncomputable def allK {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) l

@[expose] noncomputable def pkC (D : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih c => Nat.add (Nat.mod c 3) (Nat.mul 65536 (ih (Nat.div c 3)))) D k

@[expose] noncomputable def pkrC (D : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih c acc => ih (Nat.div c 3) (Nat.add (Nat.mul acc 65536) (Nat.mod c 3))) D k 0

@[expose] noncomputable def mskH (F : Fd) (R : List (Nat × Nat)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun r _ ih => Nat.add (bif Nat.beq (dotK F r.2 v) 0 then 1 else 0) (Nat.mul 2 ih)) R

@[expose] noncomputable def mskF (F : Fd) (R : List (Nat × Nat)) (f : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun r _ ih => Nat.add (bif Nat.beq (dotK F f r.1) 0 then 1 else 0) (Nat.mul 2 ih)) R

@[expose] noncomputable def addC (N : Nat) (cs : List Nat) : Nat × Nat × Bool → Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat × Nat × Bool → Nat × Nat × Bool) (fun st => st)
    (fun c _ ih st => ih (Nat.lor st.1 (Nat.shiftLeft 1 c), Nat.succ st.2.1,
      st.2.2 && Nat.blt c N && clearB st.1 c)) cs

@[expose] noncomputable def bkK (F : Fd) (D N : Nat) (R : List (Nat × Nat))
    (bk : List (Nat × List Nat × List Nat)) : Nat → Nat × Nat × Bool → Nat × Nat × Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat × Nat × Bool → Nat × Nat × Bool → Bool)
    (fun _ sf sh => sf.2.2 && sh.2.2 && Nat.beq sf.2.1 N && Nat.beq sh.2.1 N)
    (fun b _ ih prev sf sh =>
      Nat.ble prev b.1 &&
      allK (fun k => Nat.beq (mskF F R (pkrC D k)) b.1) b.2.1 &&
      allK (fun k => Nat.beq (mskH F R (pkC D k)) b.1) b.2.2 &&
      ih (Nat.succ b.1) (addC N b.2.1 sf) (addC N b.2.2 sh)) bk

@[expose] noncomputable def matchH (F : Fd) (D f : Nat) (hs : List Nat) :
    List (Nat × Nat) × Bool → List (Nat × Nat) × Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) × Bool → List (Nat × Nat) × Bool) (fun st => st)
    (fun h _ ih st =>
      let v := pkC D h
      bif Nat.beq (dotK F f v) 2 then
        ih (List.rec (motive := fun _ => List (Nat × Nat) × Bool) ([], false)
          (fun e es _ => (es, st.2 && Nat.beq e.1 v && Nat.beq e.2 f)) st.1)
      else ih st) hs

@[expose] noncomputable def matchF (F : Fd) (D : Nat) (hs fs : List Nat) :
    List (Nat × Nat) × Bool → List (Nat × Nat) × Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) × Bool → List (Nat × Nat) × Bool) (fun st => st)
    (fun k _ ih st => ih (matchH F D (pkrC D k) hs st)) fs

@[expose] noncomputable def candOK (F : Fd) (D : Nat) (bk : List (Nat × List Nat × List Nat))
    (cd : List (Nat × Nat)) : Bool :=
  let r := List.rec (motive := fun _ => List (Nat × Nat) × Bool → List (Nat × Nat) × Bool)
    (fun st => st) (fun b _ ih st => ih (matchF F D b.2.2 b.2.1 st)) bk (cd, true)
  r.2 && r.1.isEmpty

@[expose] noncomputable def eqP (a b : Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2

@[expose] noncomputable def negP (F : Fd) (D : Nat) (a : Nat × Nat) : Nat × Nat :=
  (ExclK.red F (Nat.sub (Nat.mul 3 (ones D)) a.1), ExclK.red F (Nat.sub (Nat.mul 3 (ones D)) a.2))

@[expose] noncomputable def eqPM (F : Fd) (D : Nat) (a b : Nat × Nat) : Bool :=
  eqP a b || eqP a (negP F D b)

@[expose] noncomputable def cw (F : Fd) (G : List (Nat × Nat)) (w : List Nat) (e : Nat × Nat) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) e (fun l _ ih => conjK F (nthK (0, 0) G l) ih) w

@[expose] noncomputable def tag1 (F : Fd) (D n X : Nat) (G : List (Nat × Nat)) (R1 : List Rep)
    (c : Nat × Nat) (t : List Nat) : Bool :=
  bif Nat.beq (dotK F c.2 X) 0 then t.isEmpty
  else List.rec (motive := fun _ => Bool) false
    (fun j u _ => Nat.blt j R1.length && ltAll n u && eqPM F D (cw F G u c) (nthK rep0 R1 j).1) t

@[expose] noncomputable def goodMax (rp : Rep) : Bool := Nat.blt 0 rp.2.1.2.1 && Nat.beq rp.2.2.1 1

@[expose] noncomputable def tag2 (F : Fd) (D n1 nC2 mx : Nat) (G1 C2 : List (Nat × Nat))
    (Q : List ((Nat × Nat) × ORec)) (R1 : List Rep) (c : Nat × Nat) (t1 : List Nat)
    (t : Nat × Nat × List Nat) : Bool :=
  let k := t.2.1
  bif Nat.beq t.1 0 then Nat.blt k nC2 && eqPM F D c (nthK (0, 0) C2 k)
  else bif Nat.beq t.1 1 then
    Nat.blt k nC2 &&
      (let ρ := nthK (0, 0) C2 k
       bne (Nat.beq (dotK F c.2 ρ.1) 0) (Nat.beq (dotK F ρ.2 c.1) 0))
  else bif Nat.beq t.1 2 then
    Nat.blt k Q.length && ltAll n1 t.2.2 &&
      eqPM F D (cw F G1 t.2.2 c) (nthK ((0, 0), ([], 0, 0, [], [], [], [])) Q k).1
  else Nat.beq t.1 3 && Nat.beq mx 0 &&
    List.rec (motive := fun _ => Bool) false
      (fun j _ _ => Nat.blt j R1.length && goodMax (nthK rep0 R1 j)) t1

@[expose] noncomputable def all3 {α β γ : Type} (f : α → β → γ → Bool) :
    List α → List β → List γ → Bool :=
  List.rec (motive := fun _ => List β → List γ → Bool) (fun l m => l.isEmpty && m.isEmpty)
    (fun x _ ih l m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => List.rec (motive := fun _ => Bool) false
        (fun z zs _ => f x y z && ih ys zs) m) l)

@[expose] noncomputable def ptF (P : Pt) : Fd := fdB 3 P.D

@[expose] noncomputable def baseK (P : Pt) (d : FD) : Bool :=
  let F := ptF P
  let G := gensK P
  let n := G.length
  let C := G ++ d.1.map fun e => (e.2.2.1, e.2.2.2)
  let X := pk P.D P.x
  Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 7 && allK (reflOK F) G &&
    cloP F n G d.1 n 0 C && allK (fun r => Nat.beq (dotK F r.2 X) 0) C &&
    bkK F P.D (Nat.pow 3 P.D) C d.2.1 0 (0, 0, true) (0, 0, true)

@[expose] noncomputable def candK (P : Pt) (d : FD) : Bool := candOK (ptF P) P.D d.2.1 d.2.2.1

@[expose] noncomputable def tag1K (P : Pt) (d : FD) : Bool :=
  let G := gensK P
  all2 (tag1 (ptF P) P.D G.length (pk P.D P.x) G d.2.2.2.2) d.2.2.1 d.2.2.2.1

@[expose] noncomputable def repK (P : Pt) (d : FD) : Bool :=
  let F := ptF P
  let G := gensK P
  allK (fun rp => reflOK F rp.1 && oK F P.D P.bound (G ++ [rp.1]) rp.2.1) d.2.2.2.2

@[expose] noncomputable def s2 (F : Fd) (D bnd : Nat) (G : List (Nat × Nat)) (cd : List (Nat × Nat))
    (tg1 : List (List Nat)) (R1 : List Rep) (rp : Rep) : Bool :=
  bif Nat.beq rp.2.1.2.1 0 then rp.2.2.2.2.2.isEmpty && rp.2.2.2.2.1.isEmpty
  else
    let G1 := G ++ [rp.1]
    let n1 := G1.length
    let ro := rp.2.2.2.1
    let C2 := G1 ++ ro.map fun e => (e.2.2.1, e.2.2.2)
    let Q := rp.2.2.2.2.1
    Nat.ble rp.2.2.1 1 && cloP F n1 G1 ro n1 0 C2 &&
      allK (fun q => reflOK F q.1 && Nat.beq q.2.2.1 0 && oK F D bnd (G1 ++ [q.1]) q.2) Q &&
      all3 (tag2 F D n1 (Nat.add n1 ro.length) rp.2.2.1 G1 C2 Q R1) cd tg1 rp.2.2.2.2.2

@[expose] noncomputable def s2K (P : Pt) (d : FD) : Bool :=
  allK (s2 (ptF P) P.D P.bound (gensK P) d.2.2.1 d.2.2.2.1 d.2.2.2.2) d.2.2.2.2

@[expose] noncomputable def partK (P : Pt) (d : FD) (i : Nat) : Bool :=
  bif Nat.beq i 0 then baseK P d else bif Nat.beq i 1 then candK P d
  else bif Nat.beq i 2 then tag1K P d else bif Nat.beq i 3 then repK P d else s2K P d

@[expose] noncomputable def frameK (P : Pt) (d : FD) : Bool :=
  baseK P d && candK P d && tag1K P d && repK P d && s2K P d

end CFSG.ReflExt.RXK

end
