module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.OddPt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC

@[expose] noncomputable def strictLN (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def tsK (n nw : Nat) (LR T : Nat → Nat) : Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun d ih j acc => strictLN (LR d) (fun R => strictLN (rcnt R) (fun c =>
      strictLN (T (Nat.add (roff n nw R) (Nat.mod j c))) (fun t =>
        strictLN (Nat.div j c) (fun j' => ih j' (List.cons t acc))))))

@[expose] noncomputable def apR (w m : Nat) (ts : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun t _ ih q => strictN (ih q) (fun y => pg w m t y)) ts q

@[expose] noncomputable def apL (w m : Nat) (ts : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun t _ ih q => strictN (pg w m t q) (fun y => ih y)) ts q

@[expose] noncomputable def itF (f : Nat → Nat) (k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => strictN q f) k

@[expose] noncomputable def movesK (f : Nat → Nat) (mo L p : Nat) : Bool :=
  bAnd(Nat.beq (itF f L p) p, Bool.not (Nat.beq (itF f (Nat.mod mo L) p) p))

@[expose] noncomputable def bindL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) (k []) (fun h t _ => k (List.cons h t)) l

@[expose] noncomputable def oddPtOne (n w m nw idn : Nat) (LR TR TRI : Nat → Nat) (nb mo j e : Nat) :
    Bool :=
  strictB (Nat.mod e (nat_lit 4)) (fun t =>
  strictB (Nat.mod (Nat.div e (nat_lit 4)) (nat_lit 256)) (fun L =>
  strictB (Nat.mod (Nat.div e (nat_lit 1024)) (nat_lit 65536)) (fun p =>
  strictB (Nat.div e (nat_lit 67108864)) (fun h =>
  bIf(Nat.beq t (nat_lit 0), Nat.beq (elemK n w m nw idn LR TR nb j) idn,
  bAnd(Nat.blt p n,
  bindL (tsK n nw LR TR nb j []) (fun xs =>
  bIf(Nat.beq t (nat_lit 1), movesK (fun q => apR w m xs q) mo L p,
  bAnd(Nat.beq t (nat_lit 2),
  bindL (tsK n nw LR TR nb h []) (fun hs =>
  bindL (tsK n nw LR TRI nb h []) (fun his =>
    movesK (fun q => apR w m xs (apR w m hs (apR w m xs (apL w m his q)))) mo L p)))))))))))

@[expose] noncomputable def oddPK (n w m nw idn : Nat) (LR TR TRI : Nat → Nat) (nb mo : Nat)
    (W : Nat → Nat) (lo len : Nat) : Bool :=
  allBlk lo (fun j => oddPtOne n w m nw idn LR TR TRI nb mo j (W j)) len

end CFSG.KS.SporSch.OddPt

end
