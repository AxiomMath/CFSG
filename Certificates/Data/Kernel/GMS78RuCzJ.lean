module

public import Certificates.Data.Kernel.GMS78RuNE
public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def czPc (p q : Nat) : Nat := CFSG.KC.Census.pc 128 7 p q

@[expose] noncomputable def kPointAt (GS : List Nat) (PT LK : Nat → Nat) (PAR LAB i : Nat) : Bool :=
  (fun u pa la => andB (CFSG.KC.Census.pvalid 128 7 u) <|
    andB (allN (nat_lit 6) fun k => (fun e => andB (Nat.blt e (nat_lit 2048))
      (Nat.beq (PT e) (czPc (neGet 0 GS k) u))) (fget (LK k) i 11)) <|
    orB (andB (Nat.beq i 0) (Nat.beq u (CFSG.KC.Census.pid 128 7)))
      (andB (Nat.blt 0 i) (andB (Nat.blt pa i) (andB (Nat.blt la (nat_lit 6))
        (Nat.beq u (czPc (neGet 0 GS la) (PT pa)))))))
  (PT i) (fget PAR i 11) (fget LAB i 3)

@[expose] noncomputable def czPtsK (PT : Nat → Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u _ ih i => andB (Nat.beq (PT i) u) (neStrictB (Nat.succ i) ih))

@[expose] noncomputable def kPoints (GS : List Nat) (PT : Nat → Nat) (c : CFSG.KC.Census.ArrCertP) :
    Bool :=
  andB (Nat.beq (neLen c.pts.toList) (nat_lit 2048)) <|
    andB (neAllL (fun g => CFSG.KC.Census.pvalid 128 7 g) GS) <|
    andB (Nat.beq (neLen GS) (nat_lit 6)) <|
    czPtsK PT c.pts.toList 0

@[expose] noncomputable def czKey (u : Nat) : Nat :=
  Nat.add (fget u 0 7) (Nat.add (Nat.mul (nat_lit 128) (fget u 5 7)) (Nat.mul (nat_lit 16384) (fget u 3 7)))

@[expose] noncomputable def kKeys (PT : Nat → Nat) : Bool :=
  Nat.beq (Nat.land (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => (fun b => Bool.rec (motive := fun _ => Nat) (Nat.lor S 1)
        (Nat.lor S b) (Nat.beq (Nat.land S b) 0)) (pw2 (Nat.succ (czKey (PT i))))) (nat_lit 2048))
    (nat_lit 1)) 0

@[expose] noncomputable def czColsK (LK : Nat → Nat) : List (Array Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih i => andB (Nat.beq e.size (nat_lit 6))
      (andB (allN (nat_lit 6) fun k => Nat.beq (fget (LK k) i 11) (e.getD k 0))
        (neStrictB (Nat.succ i) ih)))

@[expose] noncomputable def kCols (c : CFSG.KC.Census.ArrCertP) (LK : Nat → Nat) : Bool :=
  andB (Nat.beq (neLen c.edges.toList) (nat_lit 2048)) (czColsK LK c.edges.toList 0)

@[expose] noncomputable def kRow (LK RW : Nat → Nat) (PAR LAB : Nat) (a : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    ((fun R P L => allN (nat_lit 2048) fun b => Nat.beq (fget R b 11) (fget L (fget P b 11) 11))
      (RW a) (RW (fget PAR a 11)) (LK (fget LAB a 3)))
    ((fun R => allN (nat_lit 2048) fun b => Nat.beq (fget R b 11) b) (RW 0))
    (Nat.beq a 0)

@[expose] noncomputable def czFieldsK (w : Nat) (F : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => andB (Nat.beq (fget F i w) x) (neStrictB (Nat.succ i) ih))

@[expose] noncomputable def kParLab (c : CFSG.KC.Census.ArrCertP) (PAR LAB : Nat) : Bool :=
  andB (czFieldsK 11 PAR c.par.toList 0) (andB (czFieldsK 3 LAB c.lab.toList 0)
    (andB (Nat.beq (neLen c.par.toList) (nat_lit 2048)) (Nat.beq (neLen c.lab.toList) (nat_lit 2048))))

@[expose] noncomputable def kInv (RW : Nat → Nat) (INV a : Nat) : Bool :=
  andB (Nat.blt (fget INV a 11) (nat_lit 2048)) (Nat.beq (fget (RW a) (fget INV a 11) 11) 0)

@[expose] noncomputable def czMt (RW : Nat → Nat) (a b : Nat) : Nat := fget (RW a) b 11

@[expose] noncomputable def czLet (INV T l : Nat) : Nat :=
  (fun x => Bool.rec (motive := fun _ => Nat) (fget INV x 11) x (Nat.beq (Nat.mod l 2) 0))
    (fget T (Nat.div l 2) 11)

@[expose] noncomputable def czEv (RW : Nat → Nat) (INV T : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (czMt RW acc (czLet INV T l)) ih) w 0

@[expose] noncomputable def czPack (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 11))) l 0

@[expose] noncomputable def czEvs (RW : Nat → Nat) (INV T : Nat) (ws : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih s => Nat.lor (Nat.shiftLeft (czEv RW INV T w) s) (ih (Nat.add s 11))) ws 0

@[expose] noncomputable def czHom (RW : Nat → Nat) (PAR LAB T : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun a H => strictN H fun H =>
    Bool.rec (motive := fun _ => Nat)
      (Nat.lor H (Nat.shiftLeft (czMt RW (fget T (fget LAB a 3) 11) (fget H (fget PAR a 11) 11))
        (Nat.mul 11 a))) H (Nat.beq a 0)) (nat_lit 2048)

@[expose] noncomputable def czHomVal (RW : Nat → Nat) (PAR LAB T : Nat) (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih a => Bool.rec (motive := fun _ => Nat)
      (czMt RW (fget T (fget LAB a 3) 11) (ih (fget PAR a 11))) 0 (Nat.beq a 0)) (nat_lit 2048) a

@[expose] noncomputable def czFilter (p : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i)))
    (nat_lit 2048) []

@[expose] noncomputable def czAny (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (p x) ih) l

@[expose] noncomputable def czListEq : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false (fun y ys _ => andB (Nat.beq x y) (ih ys)) b)

@[expose] noncomputable def czRels (RW : Nat → Nat) (INV T : Nat) (rs : List (List Nat)) : Bool :=
  neAllL (fun r => Nat.beq (czEv RW INV T r) 0) rs

@[expose] noncomputable def czConjT (RW : Nat → Nat) (INV : Nat) (GI : List Nat) (d : Nat) : Nat :=
  czPack (List.rec (motive := fun _ => List Nat) []
    (fun g _ ih => List.cons (czMt RW (czMt RW (fget INV d 11) g) d) ih) GI)

@[expose] noncomputable def czConjTs (RW : Nat → Nat) (INV : Nat) (GI : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun i ih acc => ih (List.cons (czConjT RW INV GI i) acc)) (nat_lit 2048) []

@[expose] noncomputable def kPrep (RW : Nat → Nat) (PAR LAB INV : Nat) (GI : List Nat)
    (Wq Ww : List (List Nat)) (sols : List (List (List Nat))) (KQ KW : Nat)
    (FIX D3 D5 CT SOLS : List Nat) : Bool :=
  (fun G => andB (Nat.beq KQ (czHom RW PAR LAB (czEvs RW INV G Wq))) <|
    andB (Nat.beq KW (czHom RW PAR LAB (czEvs RW INV G Ww))) <|
    andB (czListEq FIX (czFilter fun a => Nat.beq (fget KQ a 11) a)) <|
    andB (czListEq D3 (czFilter fun a => Nat.beq (fget KQ (fget KQ a 11) 11)
      (czEv RW INV (czPack [0, 0, a, fget KQ a 11, 0, 0]) (neGet [] Wq 3)))) <|
    andB (czListEq D5 (czFilter fun a => Nat.beq (fget KQ (fget KQ a 11) 11)
      (czEv RW INV (czPack [0, 0, 0, 0, a, fget KQ a 11]) (neGet [] Wq 5)))) <|
    andB (czListEq CT (czConjTs RW INV GI)) <|
    andB (czListEq SOLS (List.rec (motive := fun _ => List Nat) []
      (fun s _ ih => List.cons (czEvs RW INV G s) ih) sols)) <|
    andB (Nat.beq (fget KQ (fget G 0 11) 11) (fget G 0 11)) <|
    andB (Nat.beq (fget KQ (fget G 1 11) 11) (fget G 1 11)) <|
    andB (Nat.beq (fget KQ (fget G 2 11) 11) (fget G 3 11)) <|
    andB (Nat.beq (fget KQ (fget G 4 11) 11) (fget G 5 11)) <|
    andB (neAllL (fun s => Nat.beq (neLen s) 6) sols) <|
    andB (Nat.beq (neLen GI) 6) <| andB (Nat.beq (neLen FIX) 8) (Nat.beq (neLen D3) 64))
  (czPack GI)

@[expose] noncomputable def czCodesLt (m : Nat) (rs : List (List Nat)) : Bool :=
  neAllL (neAllL fun l => Nat.blt l m) rs

@[expose] noncomputable def czCube (RW : Nat → Nat) (PAR LAB : Nat) (GI : List Nat) (KW : Nat)
    (CT : List Nat) (t : Nat) : Bool :=
  (fun phi => czAny (Nat.beq (czPack (List.rec (motive := fun _ => List Nat) []
      (fun g _ ih => List.cons (phi (phi (phi g))) ih) GI))) CT)
    (fun a => czHomVal RW PAR LAB t (fget KW a 11))

@[expose] noncomputable def kSearch (RW : Nat → Nat) (PAR LAB INV : Nat) (GI : List Nat)
    (rels1 rels3 rels5 : List (List Nat)) (KQ KW : Nat) (FIX D3 D5 CT SOLS : List Nat) (j : Nat) :
    Bool :=
  (fun a0 a1 c => orB (notB (czRels RW INV (czPack [a0, a1, 0, 0, 0, 0]) rels1))
    (allN (nat_lit 8) fun t => (fun a2 => (fun q2 =>
        orB (notB (czRels RW INV (czPack [a0, a1, a2, q2, 0, 0]) rels3))
        (neAllL (fun a4 => (fun t => orB (notB (andB (czRels RW INV t rels5)
            (czCube RW PAR LAB GI KW CT t))) (czAny (Nat.beq t) SOLS))
          (czPack [a0, a1, a2, q2, a4, fget KQ a4 11])) D5))
      (fget KQ a2 11)) (neGet 0 D3 (Nat.add (Nat.mul 8 c) t))))
  (neGet 0 FIX (Nat.div j 64)) (neGet 0 FIX (Nat.mod (Nat.div j 8) 8)) (Nat.mod j 8)

@[expose] noncomputable def czInj (K : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => (fun v => Bool.rec (motive := fun _ => Nat) (Nat.lor S 1)
        (Nat.lor S (pw2 (Nat.succ v))) (andB (Nat.blt v 2048) (Nat.beq (Nat.land S (pw2 (Nat.succ v))) 0)))
      (fget K i 11)) (nat_lit 2048)) (nat_lit 1)) 0

@[expose] noncomputable def czInvT (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => Nat.lor S (Nat.shiftLeft i (Nat.mul 11 (fget K i 11)))) (nat_lit 2048)

@[expose] noncomputable def czTab (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => Nat.lor S (Nat.shiftLeft (f i) (Nat.mul 11 i))) (nat_lit 2048)

@[expose] noncomputable def czLetterAt (RW : Nat → Nat) (INV : Nat) (GI : Nat) (KS KI : List Nat)
    (l a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (fget (neGet 0 KI (Nat.sub (Nat.div l 2) 6)) a 11)
      (fget (neGet 0 KS (Nat.sub (Nat.div l 2) 6)) a 11) (Nat.beq (Nat.mod l 2) 0))
    ((fun g => czMt RW (czMt RW (fget INV g 11) a) g) (czLet INV GI l))
    (Nat.blt l 12)

@[expose] noncomputable def kIdent (RW : Nat → Nat) (PAR LAB INV : Nat) (GI : List Nat)
    (relsJ Wq Wv Ww normX c2J HT HR : List (List Nat)) (sols : List (List (List Nat)))
    (cls : List Nat) : Bool :=
  (fun G => (fun A SL GAM KS => (fun KI =>
    andB (czCodesLt 12 relsJ) <| andB (czCodesLt 20 HR) <|
    andB (neAllL (fun s => Nat.beq (neLen s) 6) sols) <| andB (Nat.beq (neLen GI) 6) <|
    andB (czRels RW INV G relsJ) <|
    andB (allN (nat_lit 4) fun s => (fun x => allN (nat_lit 6) fun i =>
        Nat.beq (czMt RW (czMt RW (fget INV x 11) (fget (neGet 0 SL s) i 11)) x) (fget A i 11))
      (czEv RW INV G (neGet [] normX s))) <|
    andB (czRels RW INV (czEvs RW INV G c2J) relsJ) <|
    andB (allN (nat_lit 4) fun s => (fun s' AL => andB (Nat.blt s' 4) (allN (nat_lit 6) fun i =>
        Nat.beq (fget AL (fget GAM (fget G i 11) 11) 11) (fget GAM (fget (neGet 0 SL s') i 11) 11)))
      (neGet 0 cls s) (czHom RW PAR LAB (neGet 0 SL (Nat.add s 4)))) <|
    andB (neAllL czInj KS) <|
    andB (neAllL (fun r => (fun T => neAllL (fun g => Nat.beq (fget T g 11) g) GI)
        (List.rec (motive := fun _ => Nat → Nat) (fun T => T)
          (fun l _ ih T => strictN (czTab fun i => czLetterAt RW INV G KS KI l (fget T i 11)) ih)
          r (czTab fun i => i))) HR) <|
    czListEq (czFilter fun a => neAllL (fun g => Nat.beq (czMt RW a g) (czMt RW g a)) GI)
      [0, czEv RW INV G [0, 0]])
    (List.rec (motive := fun _ => List Nat) [] (fun K _ ih => List.cons (czInvT K) ih) KS))
    (czEvs RW INV G HT)
    (List.rec (motive := fun _ => List Nat) [] (fun s _ ih => List.cons (czEvs RW INV G s) ih) sols)
    (czHom RW PAR LAB (czEvs RW INV G c2J))
    [czHom RW PAR LAB (czEvs RW INV G Wq), czHom RW PAR LAB (czEvs RW INV G Wv),
      czHom RW PAR LAB (czEvs RW INV G Ww), czHom RW PAR LAB (czEvs RW INV G HT)])
  (czPack GI)

end CFSG.KC.GMS

end
