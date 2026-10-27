module

public import Certificates.Data.Kernel.S97RYK

public section

namespace CFSG.KC.WCK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KC.S97RYK CFSG.Sporadic.Th.Native
  CFSG.CGT.Timmesfeld75.WCCheck

@[expose] noncomputable def keyK (b : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => Nat.add (imgW 5 x i) (Nat.mul 32 ih)) b

@[expose] noncomputable def bitK (acc k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight acc k) 1) 1

@[expose] noncomputable def distK (b : List Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => !bitK acc (keyK b x) && ih (Nat.lor acc (Nat.shiftLeft 1 (keyK b x)))) L

@[expose] noncomputable def baseK2 (D : Data) (b : List Nat) (idP : Nat)
    (pcP pciP SP SiP cwP cwiP clP : List Nat) (zP : Nat) : Bool :=
  let n := D.n
  let k := D.pc.length
  distK b SP 0 &&
  (SP.all fun x => pcP.all fun s => memK SP (mulK n x s)) &&
  (SP.all fun x => pciP.all fun s => memK SP (mulK n x s)) &&
  (SP.all fun x => injK n x) &&
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

@[expose] noncomputable def verdictK (D : Data) (idP : Nat) (pcP : List Nat) (J : List Bool) :
    Verdict → Bool
  | .small => (idxU D J).length + 1 < 4
  | .notClosed i j => (idxU D J).contains i && (idxU D J).contains j &&
      !memUK D idP pcP J (mulK D.n (eltK D.n idP pcP i) (eltK D.n idP pcP j))
  | .bad t y g => (idxU D J).contains t && (idxU D J).contains y &&
      !Nat.beq (eltK D.n idP pcP t) idP && commK D.n (wK D g) (eltK D.n idP pcP t) &&
      !memUK D idP pcP J
        (mulK D.n (mulK D.n (wK D g) (eltK D.n idP pcP y)) (wK D (invWord g)))
  | .good d => (idxU D J).length + 1 == 16 && d.length == (selCls D J).length &&
      ((d.zip (selCls D J)).all fun q =>
        match q.2 with
        | [] => false
        | (i, _) :: _ => Nat.beq
            (mulK D.n (mulK D.n (wK D q.1) (eltK D.n idP pcP D.zIdx)) (wK D (invWord q.1)))
            (eltK D.n idP pcP i))

end CFSG.KC.WCK

end
