module

public import CFSG.LargeExtraspecial.S97RYCheck
public import Certificates.Data.Kernel.LocalQT.PermW
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S97RYK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.LargeExtraspecial.S11.PairCheck

@[expose] noncomputable def encK (n : Nat) (t : Table) : Nat := ofFnW n 5 fun i => Nat.mod (ap t i) 32

@[expose] noncomputable def mulK (n x y : Nat) : Nat := mulW n 5 x y

@[expose] noncomputable def memK (S : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a y, true, ih)) S

@[expose] noncomputable def strictK {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def bIfK {α : Type} (c : Bool) (t e : α) : α :=
  Bool.rec (motive := fun _ => α) e t c

@[expose] noncomputable def forceL {α : Type} (L : List Nat) (k : List Nat → α) : α :=
  List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun x _ ih k => strictK x fun y => ih fun L' => k (y :: L')) L k

@[expose] noncomputable def stepX (n x : Nat) {α : Type} :
    List Nat → List Nat → List Nat → (List Nat → List Nat → α) → α
  | [], E, F, k => k E F
  | s :: gs, E, F, k =>
    strictK (mulK n x s) fun y =>
      bIfK (memK E y) (stepX n x gs E F k) (stepX n x gs (y :: E) (y :: F) k)

@[expose] noncomputable def stepFr (n : Nat) (gs : List Nat) {α : Type} :
    List Nat → List Nat → List Nat → (List Nat → List Nat → α) → α
  | [], E, F, k => k E F
  | x :: fr, E, F, k => stepX n x gs E F fun E F => stepFr n gs fr E F k

@[expose] noncomputable def closeK (n : Nat) (gs : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, E, _ => E
  | fuel + 1, E, fr => stepFr n gs fr E [] fun E F =>
      List.rec (motive := fun _ => List Nat) E (fun _ _ _ => closeK n gs fuel E F) F

@[expose] noncomputable def validT (n : Nat) (t : Table) : Bool :=
  bAnd(Nat.beq t.size n, allN n fun i => Nat.blt (ap t i) n)

@[expose] noncomputable def properK (D : Data) (fuel : Nat) (J : List Bool) (c out : List Int) : Bool :=
  let gs := tabU D J ++ tabUc D J c
  let gsP := gs.map (encK D.n)
  let idP := encK D.n (idT D.n)
  let E := closeK D.n gsP fuel [idP] [idP]
  decide (D.n < 32) && gs.all (validT D.n) && validT D.n (wT D out) && memK E idP &&
    (E.all fun x => gsP.all fun s => memK E (mulK D.n x s)) && !memK E (encK D.n (wT D out))

@[expose] noncomputable def wK (D : Data) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (encK D.n (idT D.n))
    (fun l _ ih => mulK D.n (encK D.n (D.gens l)) ih) w

@[expose] noncomputable def eltK (n idP : Nat) : List Nat → Nat → Nat
  | [], _ => idP
  | s :: ss, m => mulK n (if m % 2 = 1 then s else idP) (eltK n idP ss (m / 2))

@[expose] noncomputable def commK (n x y : Nat) : Bool := Nat.beq (mulK n x y) (mulK n y x)

@[expose] noncomputable def injK (n x : Nat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => i == j || !Nat.beq (imgW 5 x i) (imgW 5 x j)

@[expose] noncomputable def baseK (D : Data) (idP : Nat) (pcP pciP SP SiP cwP cwiP clP : List Nat)
    (zP : Nat) : Bool :=
  let n := D.n
  let k := D.pc.length
  decide SP.Nodup &&
  (SP.all fun x => pcP.all fun s => memK SP (mulK n x s)) &&
  (SP.all fun x => pciP.all fun s => memK SP (mulK n x s)) &&
  (SP.all fun x => injK n x) &&
  decide (D.zIdx < 2 ^ k) && !Nat.beq zP idP && Nat.beq (mulK n zP zP) idP &&
  (pcP.all fun s => commK n zP s) &&
  (SP.all fun x => !(pcP.all fun s => commK n x s) || Nat.beq x idP || Nat.beq x zP) &&
  (cwP.all fun g => commK n g zP) &&
  (SP.all fun x => Nat.beq x idP || Nat.beq x zP || clP.any (fun y => Nat.beq y x) ||
    (!Nat.beq (mulK n x x) idP ||
      (SP.zip SiP).any (fun y => !commK n x (mulK n (mulK n y.1 x) y.2)) ||
      (cwP.zip cwiP).any (fun g =>
        !memK SP (mulK n (mulK n g.1 x) g.2) || !commK n x (mulK n (mulK n g.1 x) g.2)))) &&
  decide (0 :: D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)).Nodup &&
  ((D.cls.flatMap fun c => c.map Prod.fst).all fun i => decide (i < 2 ^ k)) &&
  (D.cls.all fun c => match c with
    | [] => false
    | (i₀, _) :: _ => c.all fun p => commK n (wK D p.2) zP &&
        Nat.beq (mulK n (mulK n (wK D p.2) (eltK n idP pcP i₀)) (wK D (invWord p.2)))
          (eltK n idP pcP p.1))

@[expose] noncomputable def memUK (D : Data) (idP : Nat) (pcP : List Nat) (J : List Bool) (t : Nat) :
    Bool :=
  Nat.beq t idP || (idxU D J).any fun i => Nat.beq (eltK D.n idP pcP i) t

@[expose] noncomputable def pverdictK (P : PData) (idP : Nat) (pcP : List Nat) (J : List Bool) :
    PVerdict → Bool
  | .size => (idxU P.D J).length + 1 != P.ord
  | .notClosed i j => (idxU P.D J).contains i && (idxU P.D J).contains j &&
      !memUK P.D idP pcP J (mulK P.D.n (eltK P.D.n idP pcP i) (eltK P.D.n idP pcP j))
  | .bad t y g =>
      let gP := wK P.D g
      let giP := wK P.D (invWord g)
      (idxU P.D J).contains t && (idxU P.D J).contains y &&
      !Nat.beq (eltK P.D.n idP pcP t) idP &&
      ((idP :: (idxU P.D J).map (eltK P.D.n idP pcP)).all fun u =>
        commK P.D.n (mulK P.D.n (mulK P.D.n gP u) giP) (eltK P.D.n idP pcP t)) &&
      !memUK P.D idP pcP J (mulK P.D.n (mulK P.D.n gP (eltK P.D.n idP pcP y)) giP)
  | .good c nIdx out =>
      strictK (wK P.D c) fun cP => strictK (wK P.D (invWord c)) fun ciP =>
      forceL ((idP :: (idxU P.D J).map (eltK P.D.n idP pcP)).map fun u =>
          mulK P.D.n (mulK P.D.n cP u) ciP) fun Uc =>
      (idxU P.D J).length + 1 == P.ord && nIdx.length == P.nCount &&
      decide nIdx.Nodup && (nIdx.all fun i => (idxU P.D J).contains i) &&
      ((idxU P.D J).all fun i => nIdx.contains i ==
        Uc.all fun t => memK Uc (mulK P.D.n (mulK P.D.n (eltK P.D.n idP pcP i) t)
          (eltK P.D.n idP pcP i))) &&
      (!P.proper || properK P.D P.fuel J c out)

@[expose] noncomputable def pairCheckK (P : PData) : Bool :=
  let D := P.D
  let n := D.n
  decide (n < 32) && decide (2 ≤ P.ord) &&
  strictK (encK n (idT n)) fun idP =>
  forceL (D.pc.map (wK D)) fun pcP =>
  forceL (D.pc.map fun w => wK D (invWord w)) fun pciP =>
  forceL ((List.range (2 ^ D.pc.length)).map (eltK n idP pcP)) fun SP =>
  forceL (SP.map (invW n 5)) fun SiP =>
  forceL (D.cw.map (wK D)) fun cwP =>
  forceL (D.cw.map fun w => wK D (invWord w)) fun cwiP =>
  forceL ((D.cls.flatMap fun c => c.map Prod.fst).map (eltK n idP pcP)) fun clP =>
  strictK (eltK n idP pcP D.zIdx) fun zP =>
  baseK D idP pcP pciP SP SiP cwP cwiP clP zP &&
    (allMasks D.cls.length).all fun J => P.pv.any fun p => p.1 == J && pverdictK P idP pcP J p.2

end CFSG.KC.S97RYK

end
