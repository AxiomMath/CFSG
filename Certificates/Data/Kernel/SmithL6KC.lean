module

public import Certificates.Data.Kernel.SmithL6KU
public import Certificates.Data.SmithL6Tr

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def idM : List Nat := [1, 2, 4, 8, 16, 32]

@[expose] def swM : List Nat := [8, 16, 32, 1, 2, 4]

@[expose] def mulM (A B : List Nat) : List Nat := B.map (apK A)

@[expose] def trM (A : List Nat) : List Nat :=
  (List.range 6).map fun r =>
    A.zipIdx.foldl (fun acc p => if p.1.testBit r then acc ||| 2 ^ p.2 else acc) 0

@[expose] def tvM (p : Nat) : List Nat :=
  (List.range 6).map fun i => if (p % 64).testBit i then 2 ^ i ^^^ p / 64 else 2 ^ i

@[expose] noncomputable def psiM : List Nat → Nat → List Nat :=
  fun G => List.rec (motive := fun _ => Nat → List Nat) (fun _ => idM)
    (fun g _ ih a => bif a.testBit 0 then mulM (tvM g) (ih (a / 2)) else ih (a / 2)) G

@[expose] def liftC (L : List Nat) : Nat → Nat → Nat
  | 0, c => c
  | 1, c => conjF (L.getD 0 0) c
  | 2, c => conjF (L.getD 1 0) c
  | 3, c => conjF (L.getD 0 0) (conjF (L.getD 1 0) c)
  | _, c => 64 * trSw (c % 64) + trSw (c / 64)

@[expose] def liftM (L : List Nat) : Nat → List Nat
  | 0 => idM
  | 1 => tvM (L.getD 0 0)
  | 2 => tvM (L.getD 1 0)
  | 3 => mulM (tvM (L.getD 0 0)) (tvM (L.getD 1 0))
  | _ => idM

@[expose] noncomputable def candC (U L : List Nat) (j a c : Nat) : Nat := uaWC U a (liftC L j c)

@[expose] noncomputable def candM (U L : List Nat) (j a : Nat) : List Nat :=
  mulM (psiM U a) (liftM L j)

@[expose] def repsC : List (Nat × Nat) := [(0, 1), (0, 10), (0, 84), (4, 0), (4, 7)]

@[expose] def recOK (RM : List (List Nat)) (j : Nat) (M e : List Nat) : Bool :=
  e.length == 13 && decide (e.headD 0 < 5) &&
    mulM (trM ((e.drop 7).take 6)) ((e.drop 1).take 6) == idM &&
    (if j < 4 then decide (e.headD 0 < 3) &&
        mulM ((e.drop 1).take 6) M == mulM (RM.getD (e.headD 0) []) ((e.drop 1).take 6)
      else decide (3 ≤ e.headD 0) &&
        mulM ((e.drop 1).take 6) (mulM M swM) ==
          mulM (mulM (RM.getD (e.headD 0) []) swM) ((e.drop 7).take 6))

@[expose] noncomputable def entryOK (T : List Nat) (C : Nat) (U L : List Nat)
    (RM : List (List Nat)) (j a : Nat) : List Nat → Bool
  | [] => T.all fun c => candC U L j a c == c
  | [x] => decide (x < 1953) && candC U L j a (candC U L j a (fldW 12 C x)) != fldW 12 C x
  | e => recOK RM j (candM U L j a) e

@[expose] noncomputable def scanC (T : List Nat) (C : Nat) (U L : List Nat)
    (RM : List (List Nat)) (j : Nat) :
    List (List Nat) → Nat → Bool :=
  fun S => List.rec (motive := fun _ => Nat → Bool) (fun a => a == 512)
    (fun e _ ih a => entryOK T C U L RM j a e && ih (a + 1)) S

@[expose] def bitsM (m : Nat) : List Nat := (List.range 64).filter fun x => x != 0 && m.testBit x

@[expose] def planeMapC (f : Nat → Nat) (m n m' n' : Nat) : Bool :=
  (bitsM m).all fun v => (bitsM n).all fun φ =>
    m'.testBit (f (64 * v + φ) / 64) && n'.testBit (f (64 * v + φ) % 64)

@[expose] def fixPlaneC (f : Nat → Nat) (m n : Nat) : Bool :=
  (bitsM m).all fun v => (bitsM n).all fun φ => f (64 * v + φ) == 64 * v + φ

@[expose] def planeK (f : Nat → Nat) (M A i i' : Nat) : Bool :=
  decide (i < 1395) && decide (i' < 1395) &&
    planeMapC f (fldW 64 M i) (fldW 64 A i) (fldW 64 M i') (fldW 64 A i')

@[expose] def pairsOf : List Nat → List (Nat × Nat)
  | i :: i' :: l => (i, i') :: pairsOf l
  | _ => []

@[expose] def dVecK (W : Nat) (P : List (Nat × Nat)) : List Nat :=
  P.map fun p => fldW 20 W p.2 ^^^ fldW 20 W p.1

@[expose] def indep6 (vs : List Nat) : Bool :=
  vs.length == 6 && (List.range 63).all fun m => trXorSel vs (m + 1) != 0

@[expose] noncomputable def repOK (U L : List Nat) (W M A k : Nat) (e : List Nat) : Bool :=
  e.length == 15 &&
    (pairsOf (e.drop 3)).all (fun p =>
      planeK (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2) M A p.1 p.2) &&
    indep6 (dVecK W (pairsOf (e.drop 3))) &&
    ((e.headD 0 == 0 &&
        planeK (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2) M A
          (e.getD 1 0) (e.getD 2 0) &&
        fB (fldW 20 W (e.getD 2 0)) (fldW 20 W (e.getD 1 0))) ||
      (e.headD 0 == 1 && decide (e.getD 1 0 < 1395) &&
        fixPlaneC (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2)
          (fldW 64 M (e.getD 1 0)) (fldW 64 A (e.getD 1 0))) ||
      (e.headD 0 == 2 && k == 3))

@[expose] def fxEdge (C : Nat) (fx : List Nat) (g u v : Nat) : Bool :=
  conjF (fldW 12 C (fx.getD g 0)) (fldW 12 C (fx.getD u 0)) == fldW 12 C (fx.getD v 0)

@[expose] noncomputable def fpOK (f : Nat → Nat) (T : List Nat) (C W M A : Nat)
    (bs : List Nat) (pl : List (Nat × Nat)) (pm um fx : List Nat) (ft : List (Nat × Nat × Nat))
    (b6 : List Nat) : Bool :=
  decide (bs.length ≤ 8) && pl.length == 20 && pm.length == 20 &&
    (pl.zip pm).all (fun q => planeK f M A q.1.1 q.1.2 &&
      trXorSel bs q.2 == fldW 20 W q.1.2 ^^^ fldW 20 W q.1.1) &&
    (List.range 20).all (fun t => trXorSel (pl.map fun p => fldW 20 W p.1) (um.getD t 0) == 2 ^ t) &&
    ((T.zipIdx.filter fun p => f p.1 == p.1).map (·.2)) == fx &&
    fx.length % 2 == 1 &&
    treeK fx.length fx.length (· == 0) (fxEdge C fx) [0] ft &&
    b6.all (fx.contains ·) && indep6 (b6.map fun x => fldW 12 C x / 64)

end CFSG.SmithL6.K
