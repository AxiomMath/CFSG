module

public import Certificates.Data.Kernel.Misc.YamakiAutM
public import Certificates.Data.Kernel.Misc.YamakiA0

public section

namespace CFSG.KD.YamakiAutC

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def patt1 (y : Nat) : Bool :=
  (Nat.beq (wordN (fun _ => y) [0, 0, 0, 0, 0, 0, 0, 0]) ONE == true) &&
    ((Nat.beq (wordN (fun _ => y) [0, 0, 0, 0]) ONE == false) && true)

@[expose] def cyOf (a b : Nat) : Nat → Nat := fun i => if i = 0 then a else b

@[expose] noncomputable def patt2 (a b : Nat) : List (List Nat) → Bool
  | [] => true
  | w :: ws => (Nat.beq (wordN (cyOf a b) w) ONE == true) && patt2 a b ws

@[expose] noncomputable def c1At (R H : Nat → Nat) (n r0 r1 i : Nat) : Bool :=
  strictY (H i) fun h => strictY (recX R 14 i) fun y =>
    cond (Nat.beq h 0) (!patt1 y)
      (Nat.blt (Nat.div (Nat.pred h) 2) n &&
        strictY (recX R 14 (Nat.div (Nat.pred h) 2)) fun x =>
          Nat.beq (MULF x y) (MULF (cond (Nat.beq (Nat.mod (Nat.pred h) 2) 0) r0 r1) x))

@[expose] noncomputable def c1Chunk (R H : Nat → Nat) (n r0 r1 L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun i => cond (Nat.blt i n) (c1At R H n r0 r1 i) true

@[expose] noncomputable def c2At (R P1 P2 : Nat → Nat) (ws : List (List Nat)) (n c h i : Nat) :
    Bool :=
  strictY h fun h => strictY (recX R 14 i) fun y =>
    cond (Nat.beq h 0) (!patt2 c y ws)
      (Nat.blt (Nat.div (Nat.pred h) 16) n &&
        strictY (recX R 14 (Nat.div (Nat.pred h) 16)) fun x =>
          Nat.beq (MULF x c) (MULF (P1 (Nat.mod (Nat.pred h) 16)) x) &&
            Nat.beq (MULF x y) (MULF (P2 (Nat.mod (Nat.pred h) 16)) x))

@[expose] noncomputable def c2Chunk (R H P1 P2 : Nat → Nat) (ws : List (List Nat))
    (n r0 r1 L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun i => cond (Nat.blt i n)
    (c2At R P1 P2 ws n r0 (H i) i && c2At R P1 P2 ws n r1 (H (Nat.add n i)) i) true

end CFSG.KD.YamakiAutC

end
