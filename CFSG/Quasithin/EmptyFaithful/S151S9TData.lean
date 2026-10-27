module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def idTab (n : Nat) : Array Nat := Array.range n

@[expose] def dcWord : List Nat := [0, 1, 2, 1, 1, 1, 1, 0, 1, 1, 2, 1, 1]

structure Idx3Wit where
  p : Nat
  xw : List Nat
  rw : List (List Nat)
  ri : List (List Nat)
  czv : List Bool

@[expose] def Idx3Wit.letters {Lab : Type} (W : Idx3Wit) (D : LatData Lab) : Array (Array Nat) :=
  (D.sTabs ++ D.mt[W.p]!).toArray

@[expose] def Idx3Wit.xT {Lab : Type} (W : Idx3Wit) (n : Nat) (D : LatData Lab) : Array Nat :=
  wordTabA (W.letters D) n W.xw

@[expose] def Idx3Wit.rT {Lab : Type} (W : Idx3Wit) (n : Nat) (D : LatData Lab) (i : Nat) : Array Nat :=
  wordTabA D.sTabs.toArray n W.rw[i]!

@[expose] def Idx3Wit.riT {Lab : Type} (W : Idx3Wit) (n : Nat) (D : LatData Lab) (i : Nat) : Array Nat :=
  wordTabA D.sTabs.toArray n W.ri[i]!

@[expose] def Idx3Wit.dcT {Lab : Type} (W : Idx3Wit) (n : Nat) (D : LatData Lab) (i : Nat) : Array Nat :=
  wordTabA #[W.rT n D i, W.xT n D, W.riT n D i] n dcWord

@[expose] def Idx3Wit.Ok {Lab : Type} [DecidableEq Lab] (W : Idx3Wit) (n : Nat)
    (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (zT : Array Nat) : Prop :=
  W.p < D.mw.size ∧ (D.mt[W.p]!).length = 1 ∧ (∀ l ∈ W.xw, l < D.sTabs.length + 1) ∧
  wordTabA #[W.xT n D] n [0, 0, 0] = idTab n ∧ W.xT n D ≠ idTab n ∧
  W.rw.length = 5 ∧ W.ri.length = 5 ∧
  (∀ i < 5, (∀ l ∈ W.rw[i]!, l < D.sTabs.length) ∧ (∀ l ∈ W.ri[i]!, l < D.sTabs.length) ∧
    wordTabA #[W.rT n D i, W.riT n D i] n [0, 1] = idTab n ∧
    act (wordTabA #[W.xT n D, W.rT n D i] n [0, 0, 1, 0]) Δ = Δ ∧
    act (wordTabA #[W.xT n D, W.rT n D i] n [0, 1, 0, 0]) Δ = Δ) ∧
  (∀ i < 5, ∀ i' < 5, W.dcT n D i = W.dcT n D i' → i = i') ∧
  W.czv.length = D.mw.size ∧
  (∀ j < D.mw.size, (W.czv[j]! = true ↔
    ∀ t ∈ D.mt[j]!, wordTabA #[zT, t] n [0, 1] = wordTabA #[zT, t] n [1, 0]))

instance {Lab : Type} [DecidableEq Lab] (W : Idx3Wit) (n : Nat) (act : Array Nat → Lab → Lab) (Δ : Lab)
    (D : LatData Lab) (zT : Array Nat) : Decidable (W.Ok n act Δ D zT) := by
  unfold Idx3Wit.Ok; infer_instance

end CFSG.Quasithin.S151S9T
