module

public import Certificates.Data.Kernel.SporSch.Co1Elem

public section

namespace CFSG.KS.SporSch.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2Shape CFSG.KS.Mathieu CFSG.KS.SporSch.M24

@[expose] noncomputable def ngetLL (l : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) l

@[expose] noncomputable def actC (CE : List (List (List Nat))) (i c : Nat) : Nat :=
  foldN (nat_lit 6) (fun j s => Nat.add s (Nat.mul
    (Nat.mod (foldN (nat_lit 6) (fun l t => Nat.add t
      (Nat.mul (dig3 c l) (nget (ngetL (ngetLL CE i) j) l))) (nat_lit 0)) (nat_lit 3))
    (Nat.pow (nat_lit 3) j))) (nat_lit 0)

@[expose] noncomputable def encG (EC : List (List Nat)) (j : Nat) : Nat :=
  foldN (nat_lit 6) (fun l s => Nat.add s (Nat.mul (Nat.mod (nget (ngetL EC j) l) (nat_lit 3))
    (Nat.pow (nat_lit 3) l))) (nat_lit 0)

@[expose] noncomputable def encNG (EC : List (List Nat)) (j : Nat) : Nat :=
  foldN (nat_lit 6) (fun l s => Nat.add s (Nat.mul
    (Nat.mod (Nat.sub (nat_lit 3) (Nat.mod (nget (ngetL EC j) l) (nat_lit 3))) (nat_lit 3))
    (Nat.pow (nat_lit 3) l))) (nat_lit 0)

@[expose] noncomputable def cOf (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun a _ => a) t

@[expose] noncomputable def pOf (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ b => Prod.rec (motive := fun _ => Nat) (fun p _ => p) b) t

@[expose] noncomputable def gOf (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ b => Prod.rec (motive := fun _ => Nat) (fun _ g => g) b) t

@[expose] noncomputable def codes (T : List (Nat × Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun t _ ih => cOf t :: ih) T

@[expose] noncomputable def lenT (T : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) T

@[expose] noncomputable def memL' (x : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) S

@[expose] noncomputable def anyG (EC : List (List Nat)) (c : Nat) : Bool :=
  bIf(allN (nat_lit 12) (fun j => bIf(Nat.beq c (encG EC j), false,
    bIf(Nat.beq c (encNG EC j), false, true))), false, true)

@[expose] noncomputable def chainK (CE : List (List (List Nat))) (C : List Nat)
    (T : List (Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih m => bAnd(bIf(Nat.beq m (nat_lit 0), true,
      strictB (pOf t) (fun p => strictB (gOf t) (fun g => bAnd(Nat.blt p m, bAnd(Nat.blt g (nat_lit 3),
        Nat.beq (cOf t) (actC CE g (nget C p))))))), ih (Nat.succ m))) T

@[expose] noncomputable def treeK (CE : List (List (List Nat))) (T : List (Nat × Nat × Nat))
    (r n : Nat) : Bool :=
  strictB (lenT T) (fun len => bAnd(Nat.beq len n,
  bAnd(distinctL (nat_lit 729) (codes T) (nat_lit 0),
  bAnd(Nat.beq (nget (codes T) (nat_lit 0)) r,
  bAnd(chainK CE (codes T) T (nat_lit 0),
    List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(allN (nat_lit 3) (fun i =>
      memL' (actC CE i c) (codes T)), ih)) (codes T))))))

@[expose] noncomputable def orbK (T₀ T₁ T₂ T₃ : List (Nat × Nat × Nat))
    (CE : List (List (List Nat))) (EC : List (List Nat)) : Bool :=
  bAnd(treeK CE T₀ (nat_lit 0) (nat_lit 1),
  bAnd(treeK CE T₁ (encG EC (nat_lit 0)) (nat_lit 24),
  bAnd(treeK CE T₂ (nat_lit 243) (nat_lit 264),
  bAnd(treeK CE T₃ (nat_lit 81) (nat_lit 440),
  bAnd(allN (nat_lit 729) (fun c => bIf(memL' c (codes T₀), true, bIf(memL' c (codes T₁), true,
    bIf(memL' c (codes T₂), true, memL' c (codes T₃))))),
    allN (nat_lit 729) (fun c => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false (anyG EC c))
      (anyG EC c) (memL' c (codes T₁))))))))

end CFSG.KS.SporSch.Orb

end
