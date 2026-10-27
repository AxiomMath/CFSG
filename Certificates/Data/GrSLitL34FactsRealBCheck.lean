module

public import Certificates.Data.GrSLitL34FactsRealCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def kGensC : List (ZMod 4 × ZMod 4) := [(1, 0), (0, 1), (1, 1), (1, 2), (2, 1), (1, 3)]

@[expose] def inKC (κ : ZMod 4 × ZMod 4) (i j : ZMod 4) : Prop :=
  ∃ m : ZMod 4, m * κ.1 = i ∧ m * κ.2 = j

instance (κ : ZMod 4 × ZMod 4) (i j : ZMod 4) : Decidable (inKC κ i j) := by
  unfold inKC
  infer_instance

abbrev MElt : Type := ℕ × ZMod 4 × ZMod 4

@[expose] def mulM (x y : MElt) : MElt :=
  (( t1Entry x.1 y.1).1, x.2.1 + y.2.1 + ((t1Entry x.1 y.1).2.1 : ZMod 4),
    x.2.2 + y.2.2 + ((t1Entry x.1 y.1).2.2.1 : ZMod 4))

@[expose] def invIdx (k : ℕ) : ℕ := ((List.range 64).find? fun k' => (t1Entry k k').1 == 0).getD 0

@[expose] def invM (x : MElt) : MElt :=
  (invIdx x.1, -((t1Entry x.1 (invIdx x.1)).2.1 : ZMod 4) - x.2.1,
    -((t1Entry x.1 (invIdx x.1)).2.2.1 : ZMod 4) - x.2.2)

@[expose] def betaRepM (i : ℕ) (x : MElt) : MElt :=
  ((alphaEntry i x.1).1,
    ((alphaEntry i x.1).2.1 : ZMod 4) +
      (x.2.1 * ((alphaEntry i 64).2.1 : ZMod 4) + x.2.2 * ((alphaEntry i 65).2.1 : ZMod 4)),
    ((alphaEntry i x.1).2.2.1 : ZMod 4) +
      (x.2.1 * ((alphaEntry i 64).2.2.1 : ZMod 4) + x.2.2 * ((alphaEntry i 65).2.2.1 : ZMod 4)))

@[expose] def betaYM (t i : ℕ) (x : MElt) : MElt :=
  mulM (mulM (t, 0, 0) (betaRepM i x)) (invM (t, 0, 0))

@[expose] def eqKM (κ : ZMod 4 × ZMod 4) (x y : MElt) : Bool :=
  x.1 == y.1 && decide (inKC κ (x.2.1 - y.2.1) (x.2.2 - y.2.2))

@[expose] def oneM : MElt := (0, 0, 0)

@[expose] def allM : List MElt :=
  (List.range 64).flatMap fun k =>
    (List.finRange 4).flatMap fun a => (List.finRange 4).map fun b => (k, (a : ZMod 4), (b : ZMod 4))

@[expose] def zT0 : List ℕ := [0, 4, 8, 12]

@[expose] def isBhM (κ : ZMod 4 × ZMod 4) (x : MElt) : Bool :=
  zT0.contains x.1 && eqKM κ (mulM x x) oneM

@[expose] def isAhM (κ : ZMod 4 × ZMod 4) (x : MElt) : Bool :=
  allM.all fun b => !isBhM κ b || eqKM κ (mulM x b) (mulM b x)

@[expose] def liftsK (κ : ZMod 4 × ZMod 4) (i : ℕ) : Bool :=
  ([0, 1, 2, 3] : List (ZMod 4)).all fun m =>
    let a : ZMod 4 := m * κ.1
    let b : ZMod 4 := m * κ.2
    decide (inKC κ (a * ((alphaEntry i 64).2.1 : ZMod 4) + b * ((alphaEntry i 65).2.1 : ZMod 4))
      (a * ((alphaEntry i 64).2.2.1 : ZMod 4) + b * ((alphaEntry i 65).2.2.1 : ZMod 4)))

@[expose] def fixBM (κ : ZMod 4 × ZMod 4) (t i : ℕ) : Bool :=
  allM.all fun x => !isBhM κ x || eqKM κ (betaYM t i x) x

@[expose] def pow4M (t i : ℕ) : Bool :=
  let y := comp 42 (wordTab (tg t)) (repTab i)
  comp 42 (comp 42 y y) (comp 42 y y) == idTab 42

@[expose] def invIdxOK : Bool := (List.range 64).all fun k => decide (invIdx k < 64) &&
  (t1Entry k (invIdx k)).1 == 0

@[noinline, expose] def c2OK : Bool :=
  invIdxOK && kGensC.all fun κ => (List.range 36).all fun i =>
    !liftsK κ i || (List.range 64).all fun t => !fixBM κ t i || pow4M t i

@[expose] def trichM (κ : ZMod 4 × ZMod 4) (Ah : List MElt) (t i : ℕ) (w : MElt) : Bool :=
  let u := fun v => mulM (mulM v (betaYM t i v)) w
  (Ah.any fun v => eqKM κ (u v) oneM) ||
    (Ah.any fun v => (mulM (u v) (u v)).1 == 0 && !eqKM κ (mulM (u v) (u v)) oneM) ||
    (Ah.all fun v => (u v).1 == 0 && eqKM κ (mulM (u v) (u v)) oneM && !eqKM κ (u v) oneM)

@[expose] def repInS : List ℕ := [0, 25, 31]

@[noinline, expose] def c6OK : Bool :=
  invIdxOK && kGensC.all fun κ =>
    let Ah := allM.filter (isAhM κ)
    (List.range 36).all fun i => repInS.contains i || !liftsK κ i ||
      (List.range 64).all fun t => !fixBM κ t i || allM.all fun w =>
        !eqKM κ (betaYM t i w) w ||
          !(allM.all fun x => eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w))) ||
          trichM κ Ah t i w

@[noinline, expose] def repSOK : Bool :=
  let ES := enumBFS 42 gensS 20160
  repInS.all fun i => found (indexOf ES.tabs) ES.tabs (repTab i)

@[noinline, expose] def realBOK : Bool := c2OK && c6OK && repSOK

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
