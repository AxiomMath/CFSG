module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.LQT.TC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def getTc (d : Nat) (L : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) L k

@[expose] noncomputable def lenTc (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def letG (idn : Nat) (G GI : List Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Nat.rec (motive := fun _ => Nat) idn (fun j _ => getTc idn G j) k)
    (fun k => getTc idn GI k) z

@[expose] noncomputable def wordTc (n w idn : Nat) (G GI : List Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun q => pcomp n w (mask w) (letG idn G GI z) q)) wd

@[expose] noncomputable def conjTc (n w T g : Nat) : Nat :=
  strictN (pinvS n w (mask w) g) (fun gi => pcomp n w (mask w) (pcomp n w (mask w) g T) gi)

@[expose] noncomputable def regTc (idn : Nat) (rev : List Nat) (len k : Nat) : Nat :=
  nIf(Nat.blt k len, getTc idn rev (Nat.sub (Nat.sub len k) (nat_lit 1)), idn)

@[expose] noncomputable def letTc (n w idn : Nat) (rev : List Nat) (len : Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Nat.rec (motive := fun _ => Nat) idn (fun j _ => regTc idn rev len j) k)
    (fun k => pinvS n w (mask w) (regTc idn rev len k)) z

@[expose] noncomputable def memTc (x : Nat) (rev : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) rev

@[expose] noncomputable def targTc (n w : Nat) (targets rev : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun A _ ih => bAnd(canonK n w (mask w) (n * w) A, bAnd(memTc A rev, ih))) targets

@[expose] noncomputable def runTc (n w idn : Nat) (prog : List (Int × Int))
    (k : List Nat → Nat → Bool) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) k
    (fun pq _ ih rev len => strictB (pcomp n w (mask w) (letTc n w idn rev len pq.1)
      (letTc n w idn rev len pq.2)) (fun x => ih (List.cons x rev) (Nat.succ len))) prog

@[expose] noncomputable def initTc (n w idn : Nat) (G GI : List Nat) (T : Nat)
    (ws : List (List Int)) (k : List Nat → Nat → Bool) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) k
    (fun wd _ ih rev len => strictB (conjTc n w T (wordTc n w idn G GI wd))
      (fun x => ih (List.cons x rev) (Nat.succ len))) ws

@[expose] noncomputable def gensTc (n w : Nat) (G GI : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun GI => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) GI)
    (fun g _ ih GI => List.rec (motive := fun _ => Bool) false
      (fun gi GI' _ => bAnd(canonK n w (mask w) (n * w) g,
        bAnd(permOK n w (mask w) (n * w) g gi, ih GI'))) GI) G GI

@[expose] noncomputable def tcK (n w : Nat) (G GI : List Nat) (T TI : Nat) (ws : List (List Int))
    (prog : List (Int × Int)) (targets : List Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(canonK n w (mask w) (n * w) T,
    bAnd(permOK n w (mask w) (n * w) T TI,
    initTc n w (pidn n w) G GI T ws (runTc n w (pidn n w) prog (fun rev _ => targTc n w targets rev))
      List.nil (nat_lit 0)))))

end CFSG.KC.LQT.TC

end
