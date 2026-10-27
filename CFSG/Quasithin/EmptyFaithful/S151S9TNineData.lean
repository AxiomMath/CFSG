module

public import Certificates.Data.CFSGNative.SporLat.Spec
public import CFSG.Quasithin.EmptyFaithful.S151S9TData

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat

structure Idx9Wit where
  p₁ : Nat
  p₆ : Nat
  x1w : List Nat
  x6w : List Nat
  rw : List (List Nat)
  ri : List (List Nat)

@[expose] def Idx9Wit.x1T {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) : Array Nat :=
  wordTabA (D.sTabs ++ D.mt[W.p₁]!).toArray n W.x1w

@[expose] def Idx9Wit.x6T {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) : Array Nat :=
  wordTabA (D.sTabs ++ D.mt[W.p₆]!).toArray n W.x6w

@[expose] def Idx9Wit.fT {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) (k : Nat) :
    Array Nat :=
  if k = 0 then W.x1T n D else if k = 1 then W.x6T n D else
  if k = 2 then wordTabA #[W.x1T n D, W.x6T n D] n [0, 1] else
  wordTabA #[W.x1T n D, W.x6T n D] n [0, 1, 1]

@[expose] def Idx9Wit.rT {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) (i : Nat) :
    Array Nat :=
  wordTabA D.sTabs.toArray n W.rw[i]!

@[expose] def Idx9Wit.riT {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) (i : Nat) :
    Array Nat :=
  wordTabA D.sTabs.toArray n W.ri[i]!

@[expose] def Idx9Wit.dcT {Lab : Type} (W : Idx9Wit) (n : Nat) (D : LatData Lab) (k i : Nat) :
    Array Nat :=
  wordTabA #[W.rT n D i, W.fT n D k, W.riT n D i] n dcWord

@[expose] def conj9Word (a b : Nat) : List Nat :=
  List.replicate ((3 - b) % 3) 1 ++ List.replicate ((3 - a) % 3) 0 ++ [2] ++ List.replicate a 0 ++
    List.replicate b 1

@[expose] def Idx9Wit.Ok {Lab : Type} [DecidableEq Lab] (W : Idx9Wit) (n : Nat)
    (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) : Prop :=
  W.p₁ < D.mw.size ∧ W.p₆ < D.mw.size ∧ (D.mt[W.p₁]!).length = 1 ∧ (D.mt[W.p₆]!).length = 1 ∧
  (∀ l ∈ W.x1w, l < D.sTabs.length + 1) ∧ (∀ l ∈ W.x6w, l < D.sTabs.length + 1) ∧
  wordTabA #[W.x1T n D] n [0, 0, 0] = idTab n ∧ W.x1T n D ≠ idTab n ∧
  wordTabA #[W.x6T n D] n [0, 0, 0] = idTab n ∧ W.x6T n D ≠ idTab n ∧
  wordTabA #[W.x1T n D, W.x6T n D] n [0, 1] = wordTabA #[W.x1T n D, W.x6T n D] n [1, 0] ∧
  W.rw.length = 5 ∧ W.ri.length = 5 ∧
  (∀ i < 5, (∀ l ∈ W.rw[i]!, l < D.sTabs.length) ∧ (∀ l ∈ W.ri[i]!, l < D.sTabs.length) ∧
    wordTabA #[W.rT n D i, W.riT n D i] n [0, 1] = idTab n ∧
    ∀ a < 3, ∀ b < 3,
      act (wordTabA #[W.x1T n D, W.x6T n D, W.rT n D i] n (conj9Word a b)) Δ = Δ) ∧
  (∀ k < 4, wordTabA #[W.fT n D k] n [0, 0, 0] = idTab n ∧
    ∀ i < 5, ∀ i' < 5, W.dcT n D k i = W.dcT n D k i' → i = i')

instance {Lab : Type} [DecidableEq Lab] (W : Idx9Wit) (n : Nat) (act : Array Nat → Lab → Lab)
    (Δ : Lab) (D : LatData Lab) : Decidable (W.Ok n act Δ D) := by
  unfold Idx9Wit.Ok; infer_instance

end CFSG.Quasithin.S151S9T
