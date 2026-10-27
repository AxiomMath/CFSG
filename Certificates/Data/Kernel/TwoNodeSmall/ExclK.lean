module

public import Certificates.Data.Kernel.TwoNodeSmall.WitK
public import Certificates.Data.CFSGNative.TwoNodeSmall.CorePos

public section

namespace CFSG.TwoNodeSmall.ExclK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK

abbrev Rec := Nat × Nat × List Nat × Nat × List Nat × Nat

structure Fd where
  p : Nat
  M : Nat
  k : Nat
  msk : Nat
  sh : Nat

@[expose] noncomputable def fdOf (p D : Nat) : Fd :=
  ⟨p, bif Nat.beq p 7 then 37 else 13, bif Nat.beq p 7 then 8 else 6, Nat.mul 7 (ones D),
    Nat.mul 16 (Nat.sub D 1)⟩

@[expose] noncomputable def pkP (p D : Nat) (v : Vec) : Nat :=
  Nat.rec (motive := fun _ => Vec → Nat) (fun _ => 0)
    (fun _ ih v => Nat.add (Nat.mod (v.headD 0) p) (Nat.mul 65536 (ih v.tail))) D v

@[expose] noncomputable def pkrP (p D : Nat) (f : Vec) : Nat :=
  Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
    (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) p))) D f 0

@[expose] noncomputable def red (F : Fd) (x : Nat) : Nat :=
  Nat.sub x (Nat.mul F.p (Nat.land (Nat.shiftRight (Nat.mul x F.M) F.k) F.msk))

@[expose] noncomputable def dotK (F : Fd) (f v : Nat) : Nat :=
  Nat.mod (Nat.land (Nat.shiftRight (Nat.mul f v) F.sh) 65535) F.p

@[expose] noncomputable def negK (F : Fd) (a : Nat) : Nat := Nat.mod (Nat.sub F.p a) F.p

@[expose] noncomputable def appK (F : Fd) (r : Nat × Nat) (v : Nat) : Nat :=
  red F (Nat.add v (Nat.mul (negK F (dotK F r.2 v)) r.1))

@[expose] noncomputable def conjK (F : Fd) (g r : Nat × Nat) : Nat × Nat :=
  (appK F g r.1, red F (Nat.add r.2 (Nat.mul (negK F (dotK F r.2 g.1)) g.2)))

@[expose] noncomputable def smulK (F : Fd) (l v : Nat) : Nat := red F (Nat.mul l v)

@[expose] noncomputable def chainK (F : Fd) (G : List (Nat × Nat)) (k : Nat) (w : List Nat) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (nthK (0, 0) G k)
    (fun j _ ih => conjK F (nthK (0, 0) G j) ih) w

@[expose] noncomputable def reflOK (F : Fd) (r : Nat × Nat) : Bool := Nat.beq (dotK F r.2 r.1) 2

@[expose] noncomputable def ltAll (n : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun j _ ih => Nat.blt j n && ih) w

@[expose] noncomputable def parOK (F : Fd) (G : List (Nat × Nat)) (n : Nat) (r : Rec) : Bool :=
  let s := chainK F G r.2.1 r.2.2.1
  let t := chainK F G r.2.2.2.1 r.2.2.2.2.1
  let l := r.2.2.2.2.2
  Nat.blt r.2.1 n && ltAll n r.2.2.1 && Nat.blt r.2.2.2.1 n && ltAll n r.2.2.2.2.1 &&
    Nat.blt 0 l && Nat.blt l F.p && reflOK F s && reflOK F t &&
    bif Nat.beq r.1 0 then Nat.beq t.1 (smulK F l s.1) && !(Nat.beq s.2 (smulK F l t.2))
    else Nat.beq t.2 (smulK F l s.2) && !(Nat.beq s.1 (smulK F l t.1))

@[expose] noncomputable def cycOK (F : Fd) (G : List (Nat × Nat)) (n s m D : Nat) (r : Rec) :
    Bool :=
  let j := r.2.1
  let j' := r.2.2.2.1
  let t := chainK F G j r.2.2.1
  let rj := nthK (0, 0) G j
  let rj' := nthK (0, 0) G j'
  let i := r.2.2.2.2.1.headD 0
  let e := Nat.shiftLeft 1 (Nat.mul 16 i)
  let a := Nat.mul (Nat.mul (dotK F rj.2 rj'.1) (dotK F rj'.2 t.1)) (dotK F t.2 rj.1)
  let b := Nat.mul (Nat.mul (dotK F rj'.2 rj.1) (dotK F t.2 rj'.1)) (dotK F rj.2 t.1)
  Nat.ble 5 F.p && Nat.ble s j && Nat.blt j (Nat.add s m) && Nat.ble s j' &&
    Nat.blt j' (Nat.add s m) && !(Nat.beq j j') && ltAll n r.2.2.1 && reflOK F t &&
    Nat.blt i D && !(Nat.beq (Nat.mod a F.p) (Nat.mod b F.p)) &&
    !(Nat.beq (appK F t (appK F rj' e)) (appK F rj' (appK F t e)))

@[expose] noncomputable def recOK (F : Fd) (G : List (Nat × Nat)) (n s m D : Nat) (r : Rec) :
    Bool :=
  bif Nat.blt r.1 2 then parOK F G n r
  else bif Nat.beq r.1 2 then cycOK F G n s m D r
  else false

@[expose] noncomputable def grpK (F : Fd) (G : List (Nat × Nat)) (X n s m D : Nat) :
    List (Nat × Nat) → List Rec → Bool :=
  List.rec (motive := fun _ => List Rec → Bool) (fun rs => rs.isEmpty)
    (fun q _ ih rs =>
      bif Nat.beq (dotK F q.2 X) 0 || !(reflOK F q) then ih rs
      else List.rec (motive := fun _ => Bool) false
        (fun r rs' _ => recOK F (G ++ [q]) n s m D r && ih rs') rs)

@[expose] def dimOf (lift : Bool) (N : Nat) : Nat := if lift then N else N - 1

@[expose] def extOf (lift : Bool) (v : Vec) (e : Nat) : Vec := if lift then v ++ [e] else v

@[expose] def inJ (N s k : Nat) : Bool := s ≤ k && k < s + (N - 3)

@[expose] def outsOf (N s : Nat) : List Nat := (List.range (N - 1)).filter fun k => !(inJ N s k)

@[expose] def optOf (p N oi : Nat) : Nat × Nat × Nat := (posOpts p N).getD oi (0, 0, 0)

@[expose] noncomputable def frameK (lift : Bool) (p N : Nat) : List (Nat × Nat) :=
  let D := dimOf lift N
  (List.range (N - 1)).map fun k =>
    (pkP p D (unitP D k), pkrP p D (extOf lift (cartanRowP p N k) (if k = 0 then 1 else 0)))

@[expose] noncomputable def xK (lift : Bool) (p N : Nat) : Nat :=
  pkP p (dimOf lift N) (extOf lift ((List.range (N - 1)).map (· + 1)) 0)

@[expose] noncomputable def vbK (lift : Bool) (p N s oi : Nat) : Nat :=
  let o := optOf p N oi
  pkrP p (dimOf lift N) (extOf lift ((List.range (N - 1)).map fun k =>
    if inJ N s k then (if k - s = o.1 then o.2.2 else 0) else 0) 0)

@[expose] def laneR (D k : Nat) : Nat := 2 ^ (16 * (D - 1 - k))

@[expose] noncomputable def ptsK (lift : Bool) (p N s oi : Nat) (cs : List Vec) :
    List (Nat × Nat) :=
  let D := dimOf lift N
  let vb := vbK lift p N s oi
  let L0 := laneR D ((outsOf N s).getD 0 0)
  let L1 := laneR D ((outsOf N s).getD 1 0)
  cs.flatMap fun c => (allVecsP p 2).map fun fr =>
    (pkP p D (extOf lift c 0), vb + fr.getD 0 0 * L0 + fr.getD 1 0 * L1)

@[expose] noncomputable def grpAt (lift : Bool) (p N s oi : Nat) (cs : List Vec) (rs : List Rec) :
    Bool :=
  let D := dimOf lift N
  let F := fdOf p D
  let G := frameK lift p N
  G.all (reflOK F) && grpK F G (xK lift p N) N s (N - 3) D (ptsK lift p N s oi cs) rs

@[expose] def dotS : Vec → Vec → Nat
  | a :: as, b :: bs => a * b + dotS as bs
  | _, _ => 0

@[expose] def satC (p : Nat) (cs : List (Vec × Nat)) (w : Vec) : Bool :=
  cs.all fun q => dotS q.1 w % p == q.2

@[expose] def enumPf (p : Nat) : Nat → List (Vec × Nat) → List Vec
  | 0, cs => if satC p cs [] then [[]] else []
  | n + 1, cs =>
    (enumPf p n ((cs.filter fun q => q.1.headD 0 == 0).map fun q => (q.1.tail, q.2))).flatMap
      fun v => ((List.range p).map (· :: v)).filter (satC p (cs.filter fun q => q.1.headD 0 != 0))

@[expose] def consC (p N s oi : Nat) : List (Vec × Nat) :=
  let o := optOf p N oi
  ((List.range (N - 1)).filter fun j => inJ N s j).map fun j =>
    (cartanRowP p N j, if j - s = o.1 then o.2.1 else 0)

@[expose] def cpars (_ : Unit := ()) : List (Nat × Nat × Nat × Nat) :=
  [(5, 5), (7, 7)].flatMap fun pN => [0, 1, 2].flatMap fun s =>
    (List.range (posOpts pN.1 pN.2).length).map fun oi => (pN.1, pN.2, s, oi)

@[expose] def csAt (i : Nat) (cs : List Vec) : Bool :=
  let q := (cpars ()).getD i (0, 0, 0, 0)
  enumPf q.1 (q.2.1 - 1) (consC q.1 q.2.1 q.2.2.1 q.2.2.2) == cs

@[expose] noncomputable def grpIdx (CS : List (List Vec)) (RS : List (List Rec)) (g : Nat) : Bool :=
  let q := (cpars ()).getD (g % 42) (0, 0, 0, 0)
  grpAt (!(Nat.blt g 42)) q.1 q.2.1 q.2.2.1 q.2.2.2 (CS.getD (g % 42) []) (RS.getD g [])

end CFSG.TwoNodeSmall.ExclK

end
