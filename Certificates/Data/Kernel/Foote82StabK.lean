module

public import Certificates.Data.Kernel.Census.Packed
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.KC.StabT919

open CFSG.KC.Census (at' pset)
open CFSG.EvenSmallLie.OmegaEightMinus (stabIdx)

structure St where
  P : Nat
  L : Nat
  D : Nat
  C : Nat
  Q : Nat
  n : Nat
  h : Nat
  R : Array Nat
  ok : Bool

@[expose] noncomputable def dec (w P : Nat) : Array Nat := Array.ofFn (n := 136) fun i => at' w P i.val

@[expose] noncomputable def decQ (Q n : Nat) : Array Nat := Array.ofFn (n := n) fun i => at' 8 Q i.val

@[expose] noncomputable def innerK (G : Nat → Nat → Nat) (c x : Nat) (t : St) (l : Nat) : St :=
  let y := G l x
  bif y < 136 && y != 0 && at' 8 t.C y == 0 then
    ⟨pset 8 t.P y x, pset 8 t.L y l, pset 16 t.D y (at' 16 t.D x + 1), pset 8 t.C y c,
      pset 8 t.Q t.n y, t.n + 1, t.h, t.R,
      t.ok && decide (x < 256) && decide (at' 16 t.D x + 1 < 65536) && decide (t.n < 136)⟩
  else t

@[expose] noncomputable def queueK (G : Nat → Nat → Nat) (c : Nat) (t : St) (_ : Nat) : St :=
  bif decide (t.h < t.n) then
    (List.range' 0 16).foldl (innerK G c (at' 8 t.Q t.h)) ⟨t.P, t.L, t.D, t.C, t.Q, t.n, t.h + 1, t.R, t.ok⟩
  else t

@[expose] noncomputable def rootK (C : Nat) (r p : Nat) : Nat := bif r == 0 && at' 8 C p == 0 then p else r

@[expose] noncomputable def colK (G : Nat → Nat → Nat) (t : St) (c : Nat) : St :=
  let r := (List.range' 1 135).foldl (rootK t.C) 0
  bif r != 0 then
    (List.range' 0 136).foldl (queueK G c)
      ⟨t.P, t.L, pset 16 t.D r 0, pset 8 t.C r c, pset 8 0 0 r, 1, 0, t.R.push r,
        t.ok && decide (r < 136)⟩
  else t

@[expose, irreducible] noncomputable def dInit : Nat := (List.range 136).foldl (fun a i => pset 16 a i 1000) 0

@[expose] noncomputable def stabTreeK (G : Nat → Nat → Nat) : St :=
  (List.range' 1 2).foldl (colK G) ⟨0, 0, dInit, 0, 0, 0, 0, #[], true⟩

@[expose] noncomputable def outK (G : Nat → Nat → Nat) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  (dec 8 (stabTreeK G).P, dec 8 (stabTreeK G).L, dec 16 (stabTreeK G).D, dec 8 (stabTreeK G).C,
    (stabTreeK G).R)

@[expose] noncomputable def stabTreeOKP (S : ℕ → ℕ → ℕ) (P L D C r₁ r₂ : ℕ) : Bool :=
  at' 8 C 0 == 0 && decide (1 ≤ r₁) && decide (r₁ < 136) && decide (1 ≤ r₂) && decide (r₂ < 136) &&
    at' 8 C r₁ == 1 && at' 8 C r₂ == 2 &&
    (List.range 135).all (fun i =>
      (at' 8 C (i + 1) == 1 || at' 8 C (i + 1) == 2) &&
        (if at' 16 D (i + 1) == 0 then i + 1 == r₁ || i + 1 == r₂ else
          decide (at' 8 P (i + 1) < 136) && decide (at' 8 L (i + 1) < stabIdx.length) &&
            decide (at' 16 D (at' 8 P (i + 1)) < at' 16 D (i + 1)) &&
            at' 8 C (at' 8 P (i + 1)) == at' 8 C (i + 1) &&
            S (stabIdx.getD (at' 8 L (i + 1)) 0) (at' 8 P (i + 1)) == i + 1)) &&
    (List.range 136).countP (fun p => at' 8 C p == 1) == 63 &&
    (List.range 136).countP (fun p => at' 8 C p == 2) == 72

end CFSG.KC.StabT919
