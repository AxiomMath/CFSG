module

public import Certificates.Data.Kernel.LocalQT.TcP
public import Certificates.Data.Kernel.LocalQT.J2Idx

public section

namespace CFSG.KC.W4C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.JX

@[expose] noncomputable def cpK (n w : Nat) (G GI : List Nat) (Z X : Nat) (wz wx : List Int)
    (prog : List (Int × Int)) (targets : List Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(gensTc n w [Z, X] [Z, X],
    wordP n w (pidn n w) G GI wz fun U UI => wordP n w (pidn n w) G GI wx fun V VI =>
      bAnd(Nat.beq (pcomp n w (mask w) U Z) (pcomp n w (mask w) Z U),
      bAnd(Nat.beq (pcomp n w (mask w) V X) (pcomp n w (mask w) X V),
        runP n w (pidn n w) prog (fun r1 _ _ => targTc n w targets r1)
          (List.cons V (List.cons U List.nil)) (List.cons VI (List.cons UI List.nil))
          (nat_lit 2))))))

@[expose] noncomputable def anyBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l ih => bIf(f (Nat.add b l), true, ih)) len

@[expose] noncomputable def zcK (b N z : Nat) (MR : Nat → Nat) : Bool :=
  bAnd(isInvJ b MR z, allN N fun k => Nat.beq (mtJ b MR z k) (mtJ b MR k z))

@[expose] noncomputable def covK (b N z : Nat) (MR IT : Nat → Nat) (reps : List Nat) : Bool :=
  allN N fun k => bIf(isInvJ b MR k, bIf(Nat.beq k z, true,
    anyBlk (nat_lit 0) (fun s => memTc (conjJ b MR IT s k) reps) N), true)

end CFSG.KC.W4C

end
