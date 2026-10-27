module

public import Init

public section

namespace CFSG.KD.S5Ext

@[expose] noncomputable def pm (i j : Nat) : Nat :=
  (i ^^^ j) ^^^ ((((i >>> 3) &&& (j >>> 1) &&& 1) ^^^ ((i >>> 4) &&& j &&& 1)) <<< 2)

@[expose] noncomputable def keyN (a b c d : Nat) : Nat := ((a * 32 + b) * 32 + c) * 32 + d

@[expose] def invsL : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 18, 20, 22, 24, 27, 28, 31]

@[expose] noncomputable def tb32 (x i : Nat) : Bool := Nat.beq ((x >>> i) &&& 1) 1

@[expose] noncomputable def cmM (CMP a : Nat) : Nat := (CMP >>> (32 * a)) &&& 4294967295

@[expose] noncomputable def sqD (a b c d : Nat) : Bool :=
  let ad := pm a d
  let cb := pm c b
  let s := pm ad ad
  Nat.beq s (pm cb cb) && !Nat.beq s 0

@[expose] noncomputable def enumD' (a b c m : Nat) (ds rest : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) rest
    (fun d _ ih => cond (tb32 m d && sqD a b c d) (keyN a b c d :: ih) ih) ds

@[expose] noncomputable def enumC' (CMP a b ma mb : Nat) (cs rest : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) rest
    (fun c _ ih => cond (tb32 ma c) (enumD' a b c (mb &&& cmM CMP c) invsL ih) ih) cs

@[expose] noncomputable def enumB' (CMP a ma : Nat) (bs rest : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) rest
    (fun b _ ih => cond (tb32 ma b) (enumC' CMP a b ma (cmM CMP b) invsL ih) ih) bs

@[expose] noncomputable def enumA' (CMP : Nat) (as : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => enumB' CMP a (cmM CMP a) invsL ih) as

@[expose] noncomputable def eqL (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun r => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) r)
    (fun x _ ih r => List.rec (motive := fun _ => Bool) false (fun y t _ => Nat.beq x y && ih t) r)
    l

@[expose] noncomputable def cmRow (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun y ih => cond (Nat.beq (pm x y) (pm y x)) (ih ||| (1 <<< y)) ih) n

@[expose] noncomputable def cmpB (CMP : Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun x ih => ih ||| (cmRow x 32 <<< (32 * x))) 32) CMP

@[expose] noncomputable def packL (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => x ||| (ih <<< w)) l

@[expose] noncomputable def packB (w : Nat) (l : List Nat) (P : Nat) : Bool := Nat.beq (packL w l) P

@[expose] noncomputable def sortLB (b : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => Nat.ble lo x && Nat.blt x b && ih (Nat.succ x)) l

@[expose] noncomputable def sortB (l : List Nat) (b : Nat) : Bool := sortLB b l 0

@[expose] noncomputable def l20 (x i : Nat) : Nat := (x >>> (20 * i)) &&& 1048575

@[expose] noncomputable def stepOK (S ke kp : Nat) : Bool :=
  Nat.beq ((S >>> (5 * (kp >>> 15))) &&& 31) (ke >>> 15) &&
  Nat.beq ((S >>> (5 * ((kp >>> 10) &&& 31))) &&& 31) ((ke >>> 10) &&& 31) &&
  Nat.beq ((S >>> (5 * ((kp >>> 5) &&& 31))) &&& 31) ((ke >>> 5) &&& 31) &&
  Nat.beq ((S >>> (5 * (kp &&& 31))) &&& 31) (ke &&& 31)

@[expose] noncomputable def treeB (S0 S1 A : Nat) (l : List (Nat × Nat × Nat)) : Nat → Bool × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat) (fun s => (true, s))
    (fun r _ ih s =>
      let ok := tb32 s r.2.2 && !tb32 s r.1 &&
        stepOK (cond (Nat.beq r.2.1 0) S0 S1) (l20 A r.1) (l20 A r.2.2)
      let x := ih (s ||| (1 <<< r.1))
      (ok && x.1, x.2)) l

@[expose] noncomputable def treeOK (S0 S1 A ide n : Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  let x := treeB S0 S1 A l (1 <<< ide)
  x.1 && Nat.beq x.2 (2 ^ n - 1)

@[expose] noncomputable def IDK : Nat := 35088

@[expose] noncomputable def lT (T x : Nat) : Nat := (T >>> (5 * x)) &&& 31

@[expose] noncomputable def homAt (T x tx : Nat) : Bool :=
  Nat.beq (lT T (pm x 1)) (pm tx (lT T 1)) && Nat.beq (lT T (pm x 2)) (pm tx (lT T 2)) &&
    Nat.beq (lT T (pm x 8)) (pm tx (lT T 8)) && Nat.beq (lT T (pm x 16)) (pm tx (lT T 16))

@[expose] noncomputable def homN (T : Nat) (n : Nat) : Bool × Nat :=
  Nat.rec (motive := fun _ => Bool × Nat) (true, 0)
    (fun x ih => let tx := lT T x; (ih.1 && homAt T x tx, ih.2 ||| (1 <<< tx))) n

@[expose] noncomputable def homT (T : Nat) : Bool :=
  let r := homN T 32
  r.1 && Nat.beq r.2 4294967295 && Nat.beq (lT T 0) 0

@[expose] noncomputable def FULL : Nat := 340282366920938463463374607431768211455

@[expose] noncomputable def tb (x i : Nat) : Bool := Nat.beq ((x >>> i) &&& 1) 1

@[expose] noncomputable def lE (ELP i : Nat) : Nat := (ELP >>> (160 * i)) &&& 1461501637330902918203684832716283019655932542975

@[expose] noncomputable def lM (MP g c : Nat) : Nat := (MP >>> (7 * (g * 128 + c))) &&& 127

@[expose] noncomputable def lI (INVP g : Nat) : Nat := (INVP >>> (7 * g)) &&& 127

@[expose] noncomputable def lS (SQP s : Nat) : Nat := (SQP >>> (128 * s)) &&& FULL

@[expose] noncomputable def lC (CATP k : Nat) : Nat := (CATP >>> (128 * k)) &&& FULL

@[expose] noncomputable def lCI (CIL t : Nat) : Nat := (CIL >>> (7 * t)) &&& 127

@[expose] noncomputable def gensOK (T k : Nat) : Bool :=
  Nat.beq (lT T 1) (k >>> 15) && Nat.beq (lT T 2) ((k >>> 10) &&& 31) &&
    Nat.beq (lT T 8) ((k >>> 5) &&& 31) && Nat.beq (lT T 16) (k &&& 31)

@[expose] noncomputable def elB (ELP KEYL lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => ih && homT (lE ELP (lo + i)) && gensOK (lE ELP (lo + i)) (l20 KEYL (lo + i))) n

@[expose] noncomputable def incB (KEYL n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => ih && Nat.blt (l20 KEYL i) (l20 KEYL (i + 1))) n

@[expose] noncomputable def rowM (MP KEYL g T : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c ih => ih && stepOK T (l20 KEYL (lM MP g c)) (l20 KEYL c))

@[expose] noncomputable def rowsM (MP ELP KEYL lo : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => ih && rowM MP KEYL (lo + i) (lE ELP (lo + i)) 128)

@[expose] noncomputable def invB (MP INVP ide KEYL : Nat) : Bool :=
  Nat.beq (l20 KEYL ide) IDK &&
    Nat.rec (motive := fun _ => Bool) true
      (fun g ih => ih && Nat.beq (lM MP g (lI INVP g)) ide && Nat.blt (lI INVP g) 128) 128

@[expose] noncomputable def sqB (MP SQP : Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) 0
    (fun g ih => ih ||| (1 <<< (128 * lM MP g g + g))) 128) SQP

@[expose] noncomputable def innB (T t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x ih => ih && Nat.beq (pm (lT T x) t) (pm t x)) 32

@[expose] noncomputable def ciB (ELP CIL : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => ih && innB (lE ELP (lCI CIL t)) t) 32

@[expose] noncomputable def bndB (CATP n : Nat) : Bool := Nat.blt CATP (2 ^ (128 * n))

@[expose] noncomputable def memS (SQP : Nat) (Cm : List Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun m _ ih => (ih.1 ||| (1 <<< m), ih.2 ||| lS SQP m)) Cm

@[expose] noncomputable def uni (MP C g : Nat) (Cm : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) C (fun m _ ih => ih ||| (1 <<< lM MP g m)) Cm

@[expose] noncomputable def kids (MP CATP C : Nat) (Cm : List Nat) (ks : List (Nat × Nat)) :
    Bool × Nat :=
  List.rec (motive := fun _ => Bool × Nat) (true, 0)
    (fun p _ ih => let K := lC CATP p.2
      (ih.1 && Nat.blt p.1 128 && Nat.beq (uni MP C p.1 Cm) K, ih.2 ||| K)) ks

@[expose] noncomputable def failOK (MP INVP C g c : Nat) : Bool :=
  tb C c && !tb C (lM MP (lM MP g c) (lI INVP g))

@[expose] noncomputable def fails (MP INVP C : Nat) (fs : List (Nat × Nat)) : Bool × Nat :=
  List.rec (motive := fun _ => Bool × Nat) (true, 0)
    (fun p _ ih => (ih.1 && failOK MP INVP C p.1 p.2, ih.2 ||| (1 <<< p.1))) fs

@[expose] noncomputable def recB3 (C : Nat) (ms : Nat × Nat) (kk ff : Bool × Nat) : Bool :=
  Nat.beq ms.1 C && kk.1 && ff.1 && Nat.beq (ms.2 &&& (FULL ^^^ (C ||| kk.2 ||| ff.2))) 0

@[expose] noncomputable def recB (MP INVP SQP CATP : Nat)
    (r : Nat × List Nat × List (Nat × Nat) × List (Nat × Nat)) : Bool :=
  recB3 r.1 (memS SQP r.2.1) (kids MP CATP r.1 r.2.1 r.2.2.1) (fails MP INVP r.1 r.2.2.2)

@[expose] noncomputable def recsB (MP INVP SQP CATP : Nat) (k0 : Nat)
    (rs : List (Nat × List Nat × List (Nat × Nat) × List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih k => Nat.beq r.1 (lC CATP k) && recB MP INVP SQP CATP r && ih (k + 1)) rs k0

@[expose] noncomputable def inL (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => Nat.beq x y || ih) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def asOK (C : Nat) (as : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => tb C a && ih) as

@[expose] noncomputable def tsOK (CIL C : Nat) (ts : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => Nat.blt t 32 && tb C (lCI CIL t) && ih) ts

@[expose] noncomputable def mdB (MP CIL C : Nat) (as : List Nat) (md : List (Nat × Nat × Nat)) :
    Nat → Bool × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat) (fun s => (true, s))
    (fun r _ ih s =>
      let base := Nat.beq r.1 0
      let v := cond base (lCI CIL r.2.1) (lM MP r.2.1 r.2.2)
      let ok := cond base (Nat.blt r.2.1 32 && tb C v) (inL r.2.1 as && tb s r.2.2)
      let x := ih (s ||| (1 <<< v))
      (ok && x.1, x.2)) md

@[expose] noncomputable def ldB (ELP C : Nat) (ts : List Nat) (ld : List (Nat × Nat × Nat)) :
    Nat → Bool × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat) (fun s => (true, s))
    (fun r _ ih s =>
      let base := Nat.beq r.1 0
      let v := cond base (lT (lE ELP r.2.1) r.2.2) (pm r.2.1 r.2.2)
      let ok := cond base (tb C r.2.1 && inL r.2.2 ts) (tb s r.2.1 && tb s r.2.2)
      let x := ih (s ||| (1 <<< v))
      (ok && x.1, x.2)) ld

@[expose] noncomputable def lMask (CIL C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i ih => cond (tb C (lCI CIL i)) (ih ||| (1 <<< i)) ih) 32

@[expose] noncomputable def witB (MP ELP CIL C : Nat)
    (w : List Nat × List Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) : Bool :=
  let m := mdB MP CIL C w.1 w.2.2.1 0
  let q := ldB ELP C w.2.1 w.2.2.2 0
  asOK C w.1 && tsOK CIL C w.2.1 && Nat.ble (lenL w.1 + lenL w.2.1) 4 &&
    m.1 && Nat.beq (C &&& (FULL ^^^ m.2)) 0 &&
    q.1 && Nat.beq (lMask CIL C &&& (4294967295 ^^^ q.2)) 0

@[expose] noncomputable def witsB (MP ELP CIL CATP : Nat) (k0 : Nat)
    (ws : List (List Nat × List Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => witB MP ELP CIL (lC CATP k) w && ih (k + 1)) ws k0

end CFSG.KD.S5Ext
