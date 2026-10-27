module

public import Certificates.Data.Kernel.LocalQT.Perm
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSecDefs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.FongPerm

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def forceL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => letB x fun x => ih fun ys => k (x :: ys)) l k

@[expose] noncomputable def mulS (n s t : Nat) : Nat := letN s fun s => letN t fun t => mul n s t

@[expose] noncomputable def powS (n s k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (one n) (fun _ acc => mulS n acc s) k

@[expose] noncomputable def selN (b : Bool) (x y : Nat) : Nat := Bool.rec (motive := fun _ => Nat) x y b

@[expose] noncomputable def getK {α : Type} (l : List α) (d : α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allLK {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => f x && ih) l

@[expose] noncomputable def anyLK {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => f x || ih) l

@[expose] noncomputable def mapK {α : Type} (f : α → Nat) (l : List α) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => f x :: ih) l

@[expose] noncomputable def appK (l r : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) r (fun x _ ih => x :: ih) l

@[expose] noncomputable def evW (n a b : Nat) (w : PW) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun h _ ih => mulS n (powS n (selN h.1 a b) h.2) ih) w

@[expose] noncomputable def evI (n : Nat) (R : List Nat) (w : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun h _ ih => mulS n (powS n (getK R (one n) h.1) h.2) ih) w

@[expose] noncomputable def regsK (n a b : Nat) (c : PGen) : List Nat :=
  appK (mapK (fun m => evW n a b m.1) c.ns) (mapK (fun m => evW n a b m.1) c.ms)

@[expose] noncomputable def lane (P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 160) k))
    (nat_lit 1461501637330902918203684832716283019655932542975)

@[expose] noncomputable def laneD (n P m k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (one n) (lane P k) (Nat.blt k m)

@[expose] noncomputable def elemsP (n : Nat) (c : PSimple) (g1 g2 : Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j P => letN P fun P => Nat.add P (Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat)
        (mulS n (laneD n P j (getK c.par (nat_lit 0) j)) (selN (getK c.gen false j) g1 g2))
        (one n) (Nat.beq j (nat_lit 0)))
      (Nat.mul (nat_lit 160) j))) m

@[expose] noncomputable def prodK (n : Nat) (S : Nat → Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n) (fun x _ ih => mulS n (S x) ih) l

@[expose] noncomputable def clsIs (o : Option (Nat × Nat)) (i : Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun p => Nat.beq p.2 i) o

@[expose] noncomputable def rowK (n : Nat) (c : PSimple) (g1 g2 N : Nat) (S : Nat → Nat) (k : Nat) :
    Bool :=
  (Nat.beq k (nat_lit 0) || Nat.blt (getK c.par (nat_lit 0) k) k) &&
  Nat.blt (getK c.suc1 (nat_lit 0) k) N && Nat.blt (getK c.suc2 (nat_lit 0) k) N &&
  Nat.beq (mulS n (S k) g1) (S (getK c.suc1 (nat_lit 0) k)) &&
  Nat.beq (mulS n (S k) g2) (S (getK c.suc2 (nat_lit 0) k)) &&
  Option.rec (motive := fun _ => Bool) (Nat.beq (S k) (one n))
    (fun p => Prod.rec (motive := fun _ => Bool) (fun u i => Nat.blt u N && Nat.blt i (lenK c.reps) &&
      Nat.beq (mulS n (S k) (S u)) (mulS n (S u) (S (getK c.reps (nat_lit 0) i)))) p)
    (getK c.cls none k)

@[expose] noncomputable def ncK (n : Nat) (c : PSimple) (g1 g2 N : Nat) (S : Nat → Nat) (i : Nat) :
    Bool :=
  allLK (getK c.nc ([], []) i).1 (fun l => Nat.blt l N && clsIs (getK c.cls none l) i) &&
  allLK (getK c.nc ([], []) i).2 (fun l => Nat.blt l N && clsIs (getK c.cls none l) i) &&
  Nat.beq (prodK n S (getK c.nc ([], []) i).1) g1 &&
  Nat.beq (prodK n S (getK c.nc ([], []) i).2) g2

@[expose] noncomputable def simpleK (n : Nat) (c : PSimple) (g1 g2 z : Nat) : Bool :=
  letB (lenK c.par) fun N => letB (elemsP n c g1 g2 N) fun P =>
  Nat.blt (nat_lit 0) N && Nat.beq (lenK c.gen) N && Nat.beq (lenK c.suc1) N &&
  Nat.beq (lenK c.suc2) N && Nat.beq (lenK c.cls) N && Nat.blt (nat_lit 0) c.o1 &&
  Nat.blt (nat_lit 0) c.o2 && Nat.beq (powS n g1 c.o1) (one n) &&
  Nat.beq (powS n g2 c.o2) (one n) &&
  allN N (fun k => rowK n c g1 g2 N (laneD n P N) k) &&
  allLK c.reps (fun r => Nat.blt r N) &&
  allN (lenK c.reps) (fun i => ncK n c g1 g2 N (laneD n P N) i) &&
  !(Nat.beq (mulS n g1 g2) (mulS n g2 g1)) &&
  Nat.beq (powS n (laneD n P N c.k3) (nat_lit 3)) (one n) &&
  !(Nat.beq (laneD n P N c.k3) (one n)) && Nat.beq (laneD n P N c.kz) z

@[expose] noncomputable def checkBaseK (n a b : Nat) (c : PGen) : Bool :=
  letB (evW n a b c.z) fun z =>
  Nat.beq (powS n z c.p) (one n) && !(Nat.beq z (one n)) &&
  allLK c.ts (fun w => letB (evW n a b w) fun t =>
    Nat.beq (mulS n t t) (one n) && !(Nat.beq t (one n)) && Nat.beq (mulS n z t) (mulS n t z)) &&
  allLK c.ns (fun m => letB (evW n a b m.1) fun x =>
    Nat.beq (mulS n x z) (mulS n (powS n z m.2.1) x) &&
      Nat.beq (mulS n x (powS n z m.2.2)) (mulS n z x)) &&
  allLK c.ms (fun m => letB (evW n a b m.1) fun x =>
    anyLK c.ts (fun w => letB (evW n a b w) fun t => Nat.beq (mulS n x t) (mulS n t x)))

@[expose] noncomputable def checkK (n a b : Nat) (c : PGen) : Bool :=
  checkBaseK n a b c &&
  forceL (regsK n a b c) fun R => Nat.beq a (evI n R c.wa) && Nat.beq b (evI n R c.wb)

@[expose] noncomputable def secK (n a b : Nat) (c : PSec) : Bool :=
  checkBaseK n a b c.base &&
  forceL (regsK n a b c.base) fun R =>
    letB (evI n R c.h1) fun g1 => letB (evI n R c.h2) fun g2 => letB (evW n a b c.base.z) fun z =>
      simpleK n c.simple g1 g2 z

end CFSG.KC.FongPerm
