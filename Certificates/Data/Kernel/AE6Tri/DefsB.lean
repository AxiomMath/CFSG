module

public import Certificates.Data.Kernel.AE6Tri.Defs

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def anyIx {α : Type} (L : List α) (f : Nat → α → Bool) (i₀ : Nat) : Bool :=
  notB (allIx L (fun i a => notB (f i a)) i₀)

@[expose] noncomputable def ptW (G w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => pg 9 (mask 9) (gl G c) ih) w

@[expose] noncomputable def invDOK (G D VL : List Nat) (W : List (List Nat)) : Bool :=
  allIx VL (fun _ i => eqN 360 9 (awN D (W.getD i [])) (gl G i)) 0

@[expose] noncomputable def tgOK (G : List Nat) (TW : List (List Nat)) (EL : List Nat)
    (U : List (List Nat)) : Bool :=
  forceMap TW (fun w => awN G w) (fun TV =>
    allIx EL (fun t c => eqN 360 9 (awN TV (U.getD t [])) (gl G c)) 0)

@[expose] noncomputable def lettersIn (L : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(bit L c, ih)) w

@[expose] noncomputable def sepOK (G : List Nat) (L p : Nat) (h : List Nat) (b : Nat) (O : List Nat) :
    Bool :=
  bAnd(allN 8 (fun c => bIf(bit L c, allIx O (fun _ q => bit (maskL O) (pg 9 (mask 9) (gl G c) q)) 0,
      true)),
    bAnd(bit (maskL O) p, bAnd(Nat.blt p (nat_lit 360),
    bAnd(allIx O (fun _ q => bAnd(Nat.blt q (nat_lit 360), bIf(Nat.beq q p, true,
      notB (allN 8 (fun c => notB (bAnd(bit L c, bAnd(Nat.beq (pg 9 (mask 9) (gl G c) p) p,
        notB (Nat.beq (pg 9 (mask 9) (gl G c) q) q))))))))) 0,
    bAnd(lettersIn L h, Nat.beq (ptW G h p) b)))))

@[expose] noncomputable def levOK (G : List Nat) (L : Nat) (F : List Nat) (b : Nat)
    (ws : List (List Nat)) : Bool :=
  bAnd(allIx ws (fun _ w => bAnd(lettersIn L w, allIx F (fun _ c => Nat.beq (ptW G w c) c) 0)) 0,
    forceMap ws (fun w => ptW G w b) distinctL)

end CFSG.KC.AE6Tri

end
