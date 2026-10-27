module

public import Certificates.Data.Kernel.SlpPc

public section

namespace CFSG.KC.HNClsL

open CFSG.KC.Ord CFSG.KC.SlpPc

@[expose] noncomputable def allL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (p a) ih) l

@[expose] noncomputable def anyL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (p a) ih) l

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def memN (x : Nat) (l : List Nat) : Bool :=
  anyL (fun y => Nat.beq x y) l

@[expose] noncomputable def nodupN (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => andB (notB (memN x xs)) ih) l

@[expose] noncomputable def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def okC (c : Nat) : Bool := andB (Nat.blt c 37) (notB (Nat.beq c 34))

@[expose] noncomputable def invC (c : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) [c] [35, 35] (Nat.beq c 35))
      [Nat.sub c 17] (Nat.blt c 34))
    [Nat.add c 17] (Nat.blt c 17)

@[expose] noncomputable def invW (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun c _ ih => List.append ih (invC c)) cs

@[expose] noncomputable def cntC (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ ih => Nat.add ih (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt 35 c))) cs

@[expose] noncomputable def evC (cs : List Nat) : Bool := Nat.beq (Nat.mod (cntC cs) 2) 0

@[expose] noncomputable def evS (pool : List (List Nat)) (s : List (Nat × Nat)) : Bool :=
  Nat.beq (Nat.mod (List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => Nat.add ih (Nat.mul p.2 (cntC (nthD List.nil pool p.1)))) s) 2) 0

@[expose] noncomputable def powM (mul : Nat → Nat → Nat) (ONE X : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun n acc => Bool.rec (motive := fun _ => Nat) (mul acc X) X (Nat.beq n 0)) e

@[expose] noncomputable def specM (mul : Nat → Nat → Nat) (ONE : Nat) (F : Nat → Nat)
    (s : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) ONE
    (fun p rest ih => List.rec (motive := fun _ => Nat) (powM mul ONE (F p.1) p.2)
      (fun _ _ _ => mul (powM mul ONE (F p.1) p.2) ih) rest) s

@[expose] noncomputable def specI (mul : Nat → Nat → Nat) (ONE : Nat) (G : Nat → Nat)
    (s : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) ONE
    (fun p rest ih => List.rec (motive := fun _ => Nat) (powM mul ONE (G p.1) p.2)
      (fun _ _ _ => mul ih (powM mul ONE (G p.1) p.2)) rest) s

@[expose] noncomputable def alphOK (mul : Nat → Nat → Nat) (ONE : Nat) (L : Nat → Nat) : Bool :=
  andB (allBelow 17 fun j => Nat.beq (mul (L j) (L (Nat.add 17 j))) ONE)
    (andB (Nat.beq (mul (L 35) (mul (L 35) (L 35))) ONE) (Nat.beq (mul (L 36) (L 36)) ONE))

@[expose] noncomputable def treeGo (mul : Nat → Nat → Nat) (GM : List Nat) (ng : Nat) :
    List Nat → List Nat → Nat → Nat → Nat → (List Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Nat → (List Nat → Nat → Bool) → Bool)
    (fun ks n h l k => andB (Nat.beq h n) (andB (Nat.beq l 0) (k ks n)))
    (fun t _ ih ks n h l k =>
      andB (Nat.blt h n) (andB (Nat.blt l ng)
        (sB (mul (nthD 0 GM l) (nthD 0 ks (Nat.sub (Nat.sub n 1) h))) fun x =>
          (fun (nx : List Nat → Nat → Bool) => Bool.rec (motive := fun _ => Bool)
              (andB (Nat.ble t n) (andB (Nat.beq x (nthD 0 ks (Nat.sub n t))) (nx ks n)))
              (nx (List.cons x ks) (Nat.succ n)) (Nat.beq t 0))
            (fun ks' n' => Bool.rec (motive := fun _ => Bool) (ih ks' n' h (Nat.succ l) k)
              (ih ks' n' (Nat.succ h) 0 k) (Nat.beq (Nat.succ l) ng)))))

@[expose] noncomputable def linesGo (mul : Nat → Nat → Nat) (ONE : Nat) (pool : List (List Nat))
    (F : Nat → Nat) (lines : List (List (Nat × Nat))) : (List (List Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (List Nat) → Bool) → Bool) (fun k => k List.nil)
    (fun s _ ih k => andB (evS pool s) (sB (specM mul ONE F s) fun x1 => sB (mul x1 x1) fun x2 =>
      sB (mul x2 x1) fun x3 => sB (mul x3 x1) fun x4 =>
        andB (Nat.beq (mul x4 x1) ONE) (andB (notB (Nat.beq x1 ONE))
          (ih fun ps => k (List.cons [x1, x2, x3, x4] ps))))) lines

@[expose] noncomputable def coverOK (ONE : Nat) (ks : List Nat) (pks : List (List Nat)) : Bool :=
  allL (fun x => orB (Nat.beq x ONE) (anyL (memN x) pks)) ks

@[expose] noncomputable def fuseOK (mul : Nat → Nat → Nat) (ONE : Nat) (pool : List (List Nat))
    (F : Nat → Nat) (nw : Nat) (WM : List Nat) (Y : Nat) :
    List (Nat × (List (Nat × Nat) × Nat)) → List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun ps => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (fun f _ ih ps => List.rec (motive := fun _ => Bool) false
      (fun p ps' _ => andB (Nat.blt f.1 nw) (andB (Nat.ble 1 f.2.2) (andB (Nat.ble f.2.2 4)
        (andB (evS pool f.2.1) (sB (specM mul ONE F f.2.1) fun g =>
          andB (Nat.beq (mul g Y) (mul Y g))
            (andB (Nat.beq (mul g (nthD ONE WM f.1)) (mul (nthD 0 p (Nat.sub f.2.2 1)) g))
              (ih ps'))))))) ps)

@[expose] noncomputable def conjGo (mul : Nat → Nat → Nat) (ONE : Nat) (pool : List (List Nat))
    (F G : Nat → Nat) (Y W : Nat) : List (List (Nat × Nat)) → Nat → (Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → (Nat → Bool) → Bool) (fun acc k => k acc)
    (fun s _ ih acc k => andB (evS pool s) (sB (specM mul ONE F s) fun g =>
      andB (Nat.beq (mul g W) (mul W g))
        (sB (mul acc (mul (mul g Y) (specI mul ONE G s))) fun acc' => ih acc' k)))

@[expose] noncomputable def witsOK (mul : Nat → Nat → Nat) (ONE : Nat) (pool : List (List Nat))
    (F G : Nat → Nat) (Y : Nat) :
    List (List (List (Nat × Nat)) × Nat) → List (List (Nat × Nat)) → List Nat → Bool :=
  List.rec (motive := fun _ => List (List (Nat × Nat)) → List Nat → Bool)
    (fun wl _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) wl)
    (fun w _ ih wl WM => List.rec (motive := fun _ => Bool) false
      (fun s wl' _ => andB (evS pool s)
        (conjGo mul ONE pool F G Y (nthD ONE WM 0) w.1 Y fun P =>
          sB (powM mul ONE P w.2) fun q =>
            andB (notB (Nat.beq q ONE)) (andB (Nat.beq (powM mul ONE q 5) ONE)
              (ih wl' (List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) WM)))))
      wl)

@[expose] noncomputable def chk (mul : Nat → Nat → Nat) (ONE : Nat) (L : Nat → Nat)
    (pool : List (List Nat)) (gens : List Nat) (nQ : Nat) (lines : List (List (Nat × Nat)))
    (fuse : List (Nat × (List (Nat × Nat) × Nat))) (wl : List (List (Nat × Nat)))
    (wits : List (List (List (Nat × Nat)) × Nat)) (tr : List Nat) : Bool :=
  andB (alphOK mul ONE L) (andB (allL (allL okC) pool) (mapS (wordP mul ONE L) pool fun PM =>
    (fun (F G : Nat → Nat) => sB (F 0) fun Y =>
      andB (allL (fun j => andB (evC (nthD List.nil pool j)) (Nat.beq (mul (F j) Y) (mul Y (F j))))
        gens)
      (mapS F gens fun GM => treeGo mul GM (lenL gens) tr [ONE] 1 0 0 fun ks n =>
        andB (Nat.beq n nQ) (andB (nodupN ks) (linesGo mul ONE pool F lines fun pks =>
          andB (coverOK ONE ks pks) (mapS (specM mul ONE F) wl fun WM =>
            andB (fuseOK mul ONE pool F (lenL wl) WM Y fuse pks) (witsOK mul ONE pool F G Y wits wl WM))))))
      (nthD ONE PM) (fun j => wordP mul ONE L (invW (nthD List.nil pool j)))))

end CFSG.KC.HNClsL

end
