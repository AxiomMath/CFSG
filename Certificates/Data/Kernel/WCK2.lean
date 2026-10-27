module

public import Certificates.Data.Kernel.WCK

public section

namespace CFSG.KC.WCK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KC.S97RYK CFSG.Sporadic.Th.Native
  CFSG.CGT.Timmesfeld75.WCCheck

@[expose] noncomputable def distF (f : Nat → Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => !bitK acc (f x) && ih (Nat.lor acc (Nat.shiftLeft 1 (f x)))) L

@[expose] noncomputable def injK2 (n x : Nat) : Bool := distF (imgW 5 x) (List.range n) 0

@[expose] noncomputable def packP (W : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih W)) L

@[expose] noncomputable def mkTI (b : List Nat) (L : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih j acc => strictK (Nat.lor acc (Nat.shiftLeft j (Nat.mul 11 (keyK b x))))
      fun acc' => ih (Nat.succ j) acc') L

@[expose] noncomputable def chkP (W P : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => Nat.beq (imgW W P j) x && ih (Nat.succ j)) L

@[expose] noncomputable def memP (b : List Nat) (W len SPk TI y : Nat) : Bool :=
  strictK (imgW 11 TI (keyK b y)) fun j => Nat.blt j len && Nat.beq (imgW W SPk j) y

@[expose] noncomputable def baseK3 (D : Data) (b : List Nat) (idP : Nat)
    (pcP pciP SP SiP cwP cwiP clP : List Nat) (zP len SPk TI : Nat) : Bool :=
  let n := D.n
  let k := D.pc.length
  let W := Nat.mul 5 n
  distK b SP 0 &&
  (SP.all fun x => pcP.all fun s => memP b W len SPk TI (mulK n x s)) &&
  (SP.all fun x => pciP.all fun s => memP b W len SPk TI (mulK n x s)) &&
  (SP.all fun x => injK2 n x) &&
  decide (D.zIdx < 2 ^ k) && !Nat.beq zP idP && Nat.beq (mulK n zP zP) idP &&
  (pcP.all fun s => commK n zP s) &&
  (SP.all fun x => !(pcP.all fun s => commK n x s) || Nat.beq x idP || Nat.beq x zP) &&
  (cwP.all fun g => commK n g zP) &&
  (SP.all fun x => Nat.beq x idP || Nat.beq x zP || clP.any (fun y => Nat.beq y x) ||
    (!Nat.beq (mulK n x x) idP ||
      (cwP.zip cwiP).any (fun g =>
        !memK SP (mulK n (mulK n g.1 x) g.2) || !commK n x (mulK n (mulK n g.1 x) g.2)) ||
      (SP.zip SiP).any (fun y => !commK n x (mulK n (mulK n y.1 x) y.2)))) &&
  decide (0 :: D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)).Nodup &&
  ((D.cls.flatMap fun c => c.map Prod.fst).all fun i => decide (i < 2 ^ k)) &&
  (D.cls.all fun c => match c with
    | [] => false
    | (i₀, _) :: _ => c.all fun p => commK n (wK D p.2) zP &&
        Nat.beq (mulK n (mulK n (wK D p.2) (eltK n idP pcP i₀)) (wK D (invWord p.2)))
          (eltK n idP pcP p.1))

@[expose] noncomputable def wcCheckK2 (D : Data) (b : List Nat) : Bool :=
  let n := D.n
  decide (n < 32) &&
  strictK (encK n (idT n)) fun idP =>
  forceL (D.pc.map (wK D)) fun pcP =>
  forceL (D.pc.map fun w => wK D (invWord w)) fun pciP =>
  forceL ((List.range (2 ^ D.pc.length)).map (eltK n idP pcP)) fun SP =>
  forceL (SP.map (invW n 5)) fun SiP =>
  forceL (D.cw.map (wK D)) fun cwP =>
  forceL (D.cw.map fun w => wK D (invWord w)) fun cwiP =>
  forceL ((D.cls.flatMap fun c => c.map Prod.fst).map (eltK n idP pcP)) fun clP =>
  strictK (eltK n idP pcP D.zIdx) fun zP =>
  strictK SP.length fun len =>
  strictK (packP (Nat.mul 5 n) SP) fun SPk =>
  strictK (mkTI b SP 0 0) fun TI =>
  chkP (Nat.mul 5 n) SPk SP 0 &&
  baseK3 D b idP pcP pciP SP SiP cwP cwiP clP zP len SPk TI &&
    (allMasks D.cls.length).all fun J =>
      D.verdicts.any fun p => p.1 == J && verdictK D idP pcP J p.2

end CFSG.KC.WCK

end
