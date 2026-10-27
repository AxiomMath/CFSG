module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.M11

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.Mathieu

@[expose] noncomputable def enumFrom (n w m nw : Nat) (LR TR : Nat → Nat) (p : Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ g s => nIf(p g, Nat.succ s, s))
    (fun _ ih i g s => strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun k s => strictN (pcomp n w m g (TR (Nat.add (roff n nw R) k)))
        (fun h => ih (Nat.succ i) h s)) s))

@[expose] noncomputable def cntOrdK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb g₀ e k₀ : Nat) :
    Nat :=
  strictN (LR (nat_lit 0)) (fun R =>
    enumFrom n w m nw LR TR (fun g => ordIs n w m idn g (Nat.sub e (nat_lit 1)))
      (Nat.sub nb (nat_lit 1)) (nat_lit 1) (pcomp n w m g₀ (TR (Nat.add (roff n nw R) k₀)))
      (nat_lit 0))

@[expose] noncomputable def abOK (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => strictB (icode z) (fun c =>
    bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.ble c (nat_lit 5), ih)))) wd

@[expose] noncomputable def abWordK (n w m idn A Ai B Bi : Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun z _ ih => strictN ih (fun T => strictN (icode z)
    (fun c => pcomp n w m (nIf(Nat.beq c (nat_lit 2), A, nIf(Nat.beq c (nat_lit 3), Ai,
      nIf(Nat.beq c (nat_lit 4), B, Bi)))) T))) wd

@[expose] noncomputable def powK (n w m idn p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idn (fun _ ih => strictN ih (fun q => pcomp n w m p q)) e

@[expose] noncomputable def xyWordK (n w m idn x y xi yi : Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun l _ ih => strictN ih (fun T =>
    pcomp n w m (nIf(Nat.beq l (nat_lit 0), x, nIf(Nat.beq l (nat_lit 1), y,
      nIf(Nat.beq l (nat_lit 2), xi, yi)))) T)) wd

@[expose] noncomputable def ordE (n w m idn g e : Nat) : Bool :=
  bIf(Nat.beq e (nat_lit 0), true, ordIs n w m idn g (Nat.sub e (nat_lit 1)))

@[expose] noncomputable def wordOrdK (n w m idn mx my : Nat) (ws : List (List Nat × Nat))
    (x y : Nat) : Bool :=
  strictB (powK n w m idn x (Nat.sub mx (nat_lit 1))) (fun xi =>
  strictB (powK n w m idn y (Nat.sub my (nat_lit 1))) (fun yi =>
  List.rec (motive := fun _ => Bool) true (fun p _ ih => Prod.rec (motive := fun _ => Bool)
    (fun wd e => bAnd(ordE n w m idn (xyWordK n w m idn x y xi yi wd) e, ih)) p) ws))

@[expose] noncomputable def cntWordK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb mx my : Nat)
    (ws : List (List Nat × Nat)) (R k₀ : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun R0 =>
    enumFrom n w m nw LR TR (fun y => bAnd(ordIs n w m idn y (Nat.sub my (nat_lit 1)),
        wordOrdK n w m idn mx my ws R y))
      (Nat.sub nb (nat_lit 1)) (nat_lit 1) (TR (Nat.add (roff n nw R0) k₀)) (nat_lit 0))

@[expose] noncomputable def elemR (n w m nw : Nat) (LR TR : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun d ih j acc => strictN (LR d) (fun R => strictN (rcnt R) (fun c =>
      strictN (pcomp n w m (TR (Nat.add (roff n nw R) (Nat.mod j c))) acc) (fun acc' =>
        ih (Nat.div j c) acc'))))

@[expose] noncomputable def elemK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb j : Nat) : Nat :=
  elemR n w m nw LR TR nb j idn

@[expose] noncomputable def ordK (LR : Nat → Nat) (nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun d ih => Nat.mul (rcnt (LR d)) ih) nb

@[expose] noncomputable def cw1 (n w m x h : Nat) : Nat :=
  pcomp n w m x (pcomp n w m h (pcomp n w m x (pinvS n w m h)))

@[expose] noncomputable def witK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb N mo x c : Nat) :
    Bool :=
  bIf(Nat.beq c (nat_lit 0), false, strictB (Nat.sub c (nat_lit 1)) (fun c' =>
    bIf(Nat.blt c' N,
      strictB (elemK n w m nw idn LR TR nb c') (fun h =>
        bIf(Nat.beq (powK n w m idn (cw1 n w m x h) mo) idn, false, true)),
      strictB (Nat.sub c' N) (fun c2 => bIf(Nat.blt c2 (Nat.mul N N),
        strictB (elemK n w m nw idn LR TR nb (Nat.div c2 N)) (fun h1 =>
        strictB (elemK n w m nw idn LR TR nb (Nat.mod c2 N)) (fun h2 =>
          bIf(Nat.beq (powK n w m idn (pcomp n w m (cw1 n w m x h1)
              (pcomp n w m h2 (pcomp n w m x (pinvS n w m h2)))) mo) idn, false, true))),
        false)))))

@[expose] noncomputable def oddK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb mo : Nat)
    (W : Nat → Nat) (lo len : Nat) : Bool :=
  strictB (ordK LR nb) (fun N => allBlk lo (fun j =>
    strictB (elemK n w m nw idn LR TR nb j) (fun x =>
      bIf(Nat.beq x idn, true, bIf(Nat.beq (powK n w m idn x mo) idn,
        witK n w m nw idn LR TR nb N mo x (W j), true)))) len)

end CFSG.KS.SporSch.MOC

end
