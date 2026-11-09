module

public import Certificates.Data.Kernel.B433Alt.Om

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

@[expose] noncomputable def sF (v : Nat) (k : Nat → Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (k v) (k v) (Nat.beq v (nat_lit 0))

theorem sF_eq (v : Nat) (k : Nat → Nat) : sF v k = k v := by
  unfold sF
  cases Nat.beq v 0 <;> rfl

theorem sN_eq (v : Nat) (k : Nat → Nat) : sN v k = k v := by cases v <;> rfl

@[expose] noncomputable def netApp19F (MS : Nat → Nat) (c x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun t acc => sF acc (fun a => CFSG.KC.MonsterConv.Perm.dsw
      (CFSG.KC.MonsterConv.Perm.stageShift (nat_lit 19) t) (MS (Nat.add (Nat.mul (nat_lit 37) c) t)) a))
    (nat_lit 37)

@[expose] noncomputable def appSeg19F (MS : Nat → Nat) (w a n X : Nat) : Nat :=
  sN (wLen w) (fun len =>
    Nat.rec (motive := fun _ => Nat) X
      (fun i acc => sF acc (fun x =>
        netApp19F MS (wAt w (Nat.sub (Nat.sub len (nat_lit 1)) (Nat.add a i))) x)) n)

theorem netApp19_eq_F : @netApp19 = @netApp19F := by
  funext MS c x
  unfold netApp19 netApp19F
  simp only [sN_eq, sF_eq]

theorem appSeg19_eq_F : @appSeg19 = @appSeg19F := by
  funext MS w a n X
  unfold appSeg19 appSeg19F
  simp only [sN_eq, sF_eq, netApp19_eq_F]

@[expose] noncomputable def wordOn1F (MS : Nat → Nat) (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun c _ ih X => sF (netApp19F MS c X) ih) w X

theorem wordOn1F_cons (MS : Nat → Nat) (c : Nat) (w : List Nat) (X : Nat) :
    wordOn1F MS (c :: w) X = wordOn1F MS w (netApp19 MS c X) := by
  rw [netApp19_eq_F]
  show sF (netApp19F MS c X) (fun Y => wordOn1F MS w Y) = _
  rw [sF_eq]

@[expose] noncomputable def relPOK (MS : Nat → Nat) (w : List Nat) (u : Nat) : Bool :=
  Nat.beq (wordOn1F MS w (CFSG.KC.MonsterConv.Perm.idPlane OW u))
    (CFSG.KC.MonsterConv.Perm.idPlane OW u)

section Seg
variable (MS RD RW PW CB : Nat → Nat) (LIVE : Nat) (RN RL GS XO SJ ST SA SN STL : Nat → Nat)
  (NS : Nat)

@[expose] noncomputable def segChkF (k : Nat) : Bool :=
  sB (SJ k) fun j => sB (ST k) fun s => sB (SA k) fun a => sB (SN k) fun n =>
  sB (genOf GS j s) fun g =>
    andB (Nat.blt k NS) (andB (genOK RD j g) (andB (Nat.ble (Nat.add a n) (wLen (RW g)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (SJ (Nat.sub k (nat_lit 1))) j) (andB (Nat.beq (ST (Nat.sub k (nat_lit 1))) s)
          (andB (Nat.beq (Nat.add (SA (Nat.sub k (nat_lit 1))) (SN (Nat.sub k (nat_lit 1)))) a)
            (Nat.beq (appSeg19F MS (RW g) a n (XO (Nat.sub k (nat_lit 1)))) (XO k)))))
        (Nat.beq (appSeg19F MS (RW g) (nat_lit 0) n (eOf RD PW CB LIVE RN RL XO STL j s)) (XO k))
        (Nat.beq a (nat_lit 0)))))

theorem segChk_eq_F (k : Nat) :
    segChk MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k =
      segChkF MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k := by
  unfold segChk segChkF
  rw [appSeg19_eq_F]

end Seg

end CFSG.KC.B4A

end
