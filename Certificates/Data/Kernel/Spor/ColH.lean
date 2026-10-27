module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.MonsterConv.PermValid

public section

namespace CFSG.KS.ColH

open CFSG.KC.Enum CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def lane16 (c j : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 16) j)) (nat_lit 65535)

@[expose] noncomputable def spM (M : Nat) : Nat := Nat.mul (repU (nat_lit 128) M) (nat_lit 65535)

@[expose] noncomputable def vecK (M c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 16) r)) (spM M))
      (Nat.mul (Nat.mul (nat_lit 128) M) r))) (nat_lit 8)

@[expose] noncomputable def lowK (M : Nat) : Nat :=
  Nat.mul (repU (nat_lit 128) (Nat.mul (nat_lit 8) M)) (nat_lit 18446744073709551615)

@[expose] noncomputable def offK (M : Nat) : Nat :=
  Nat.mul (repU (nat_lit 128) (Nat.mul (nat_lit 8) M)) (nat_lit 14695981039346656037)

@[expose] noncomputable def hgoK (M : Nat) (C : Nat → Nat) (L : Nat) (rem : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih i h => strictN
      (Nat.land (Nat.mul (Nat.xor h (vecK M (C i))) (nat_lit 1099511628211)) L)
      (fun h' => ih (Nat.succ i) h')) rem

@[expose] noncomputable def hashColK (M n : Nat) (C : Nat → Nat) : Nat :=
  strictN (lowK M) (fun L => hgoK M C L n (nat_lit 0) (offK M))

@[expose] noncomputable def laneH (M H j : Nat) : Nat :=
  Nat.land (Nat.shiftRight H (Nat.mul (nat_lit 128) (Nat.add (Nat.mul M (Nat.mod j (nat_lit 8)))
    (Nat.div j (nat_lit 8))))) (nat_lit 18446744073709551615)

@[expose] noncomputable def hsortK (M H cnt HS HSI i : Nat) : Bool :=
  strictB (lane16 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (lane16 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      Nat.blt (laneH M H s) (laneH M H (lane16 HS (Nat.succ i))), true))))

@[expose] noncomputable def expP (kL P : Nat) : Nat :=
  (fun W => Nat.lor
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun u acc => Nat.lor acc (Nat.shiftLeft (idPlane W u) (Nat.mul W u))) (nat_lit 4))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun u acc => Nat.lor acc (Nat.shiftLeft
        (Nat.mul (Nat.land (Nat.shiftRight P u) (repU (nat_lit 16) (Nat.shiftLeft (nat_lit 1) kL)))
          (nat_lit 65535))
        (Nat.mul W (Nat.add u (nat_lit 4))))) kL))
    (Nat.shiftLeft (nat_lit 1) (Nat.add kL (nat_lit 4)))

@[expose] noncomputable def pinK (kL N P : Nat) : Bool :=
  (fun k => (fun W => bAnd(netValid k N,
      Nat.beq (netApply k W (repU W k) N (idP k)) (expP kL P)))
    (Nat.shiftLeft (nat_lit 1) k)) (Nat.add kL (nat_lit 4))

@[expose] noncomputable def colSlK (k N w m G : Nat) (C : Nat → Nat) (lo len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun d ih => strictB (Nat.add lo d) (fun i => bAnd(
      Nat.beq (netApply k (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1) N (C (pg w m G i))) (C i), ih)))
    len

@[expose] noncomputable def idxK (cnt : Nat) (PAR LAB POS : Nat) (PI : Nat → Nat) (i : Nat) : Bool :=
  (fun par lab => bAnd(
    bIf(Nat.beq i (nat_lit 0), bAnd(Nat.beq (par i) (nat_lit 0), Nat.beq (lab i) (nat_lit 0)),
      bAnd(Nat.blt (par i) i, bAnd(Nat.blt (lab i) (nat_lit 2),
      bAnd(Nat.beq (lane16 POS (Nat.add (Nat.mul (nat_lit 2) (par i)) (lab i))) i,
        bIf(Nat.blt (Nat.succ i) cnt,
          bIf(Nat.blt (par i) (par (Nat.succ i)), true,
            bAnd(Nat.beq (par i) (par (Nat.succ i)), Nat.blt (lab i) (lab (Nat.succ i)))), true))))),
    allN (nat_lit 2) (fun l => strictB (lane16 POS (Nat.add (Nat.mul (nat_lit 2) i) l)) (fun q =>
      bAnd(Nat.blt q cnt, bAnd(Nat.beq (lane16 (PI l) q) i,
        bIf(Nat.beq q (nat_lit 0), true,
          bIf(Nat.blt i (par q), false, bIf(Nat.beq i (par q), Nat.ble (lab q) l, true)))))))))
    (fun k => lane16 PAR k) (fun k => lane16 LAB k)

@[expose] noncomputable def rootK (C : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun i => Nat.beq (lane16 (C i) (nat_lit 0)) i)

@[expose] noncomputable def laneEqK (C : Nat → Nat) (n w m j X : Nat) : Bool :=
  allN n (fun i => Nat.beq (lane16 (C i) j) (pg w m X i))

end CFSG.KS.ColH

end
