module

public import CFSG.Walter.Ree.Bombieri.PExpr
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Elim

open PE

@[expose] def atomDef : ℕ → PE
  | 0 => 1 + var 1 * var 0 ^ 2
  | 1 => 1 + var 2 * var 1 ^ 2
  | 2 => 1 + var 3 * var 2 ^ 2
  | 3 => var 1 * var 0 * var 4 - (1 + var 1 * var 0 ^ 2)
  | 4 => var 2 * var 1 * (1 + var 1 * var 0 ^ 2) - (1 + var 2 * var 1 ^ 2) * var 4 ^ 2
  | 5 => (1 + var 2 * var 1 ^ 2) * var 4 ^ 4
  | 6 => var 3 * var 2 * ((1 + var 2 * var 1 ^ 2) * var 4 ^ 4) -
      (1 + var 3 * var 2 ^ 2) * (1 + var 1 * var 0 ^ 2) ^ 2
  | _ => 0

@[expose] def vz0 : PE := var 0
@[expose] def vz1 : PE := var 1
@[expose] def vz2 : PE := var 2
@[expose] def vz3 : PE := var 3
@[expose] def vy : PE := var 4
@[expose] def aζ0 : PE := atom 0
@[expose] def aζ2 : PE := atom 2
@[expose] def aU0 : PE := atom 3
@[expose] def aU1 : PE := atom 4
@[expose] def aW : PE := atom 5
@[expose] def aU2 : PE := atom 6

@[expose] def a0 : PE := vz1 * vy ^ 2
@[expose] def b0 : PE := -(vz1 * vy ^ 2 - aζ0 + vy ^ 2)
@[expose] def c0 : PE := -aζ0
@[expose] def e0 : PE := vy ^ 2
@[expose] def b1 : PE := (aU0 ^ 2 - vy ^ 2) ^ 2
@[expose] def d1 : PE := -((aU0 + vy) ^ 2 * vy ^ 3)
@[expose] def e1 : PE := -((vz0 - vy + 1) * aU0 ^ 2 * vy ^ 2)
@[expose] def f1 : PE := vz0 * (aU0 - vy) ^ 2 * vy ^ 2
@[expose] def a2 : PE := vz3 * (aU2 - aW) ^ 2 * aW ^ 2 * aU1 ^ 2 * (aU1 + aζ0) ^ 2
@[expose] def b2 : PE :=
  -((vz3 * aW ^ 2 - aζ2 * aζ0 ^ 4 + aW ^ 2) * aU2 ^ 2 * (aU1 - aζ0) ^ 2 * (aU1 + aζ0) ^ 2)
@[expose] def c2 : PE := -(aζ2 * aζ0 ^ 4 * (aU2 + aW) ^ 2 * (aU1 - aζ0) ^ 2 * aU1 ^ 2)
@[expose] def e2 : PE := (aU2 ^ 2 - aW ^ 2) ^ 2 * aU1 ^ 2 * aζ0 ^ 2
@[expose] def b3 : PE := (aU1 ^ 2 - aζ0 ^ 2) ^ 2
@[expose] def d3 : PE := -(aW * (aU1 + aζ0) ^ 2)
@[expose] def e3 : PE := -((vz2 * aζ0 ^ 2 - aW + aζ0 ^ 2) * aU1 ^ 2)
@[expose] def f3 : PE := vz2 * (aU1 - aζ0) ^ 2 * aζ0 ^ 2

@[expose] def ent : Fin 12 → Fin 12 → PE :=
  ![![b1, 0, 0, 0, d1, e1, f1, 0, 0, 0, 0, 0],
    ![0, a0, 0, 0, b0, c0, 0, 0, e0, 0, 0, 0],
    ![0, 0, b0, 0, a0, 0, c0, 0, 0, 0, 0, e0],
    ![0, 0, 0, c0, 0, a0, b0, 0, 0, e0, 0, 0],
    ![b3, 0, 0, 0, d3, e3, f3, 0, 0, 0, 0, 0],
    ![0, a2, 0, 0, b2, c2, 0, 0, e2, 0, 0, 0],
    ![0, 0, b2, 0, a2, 0, c2, 0, 0, 0, 0, e2],
    ![0, 0, 0, 0, b1, 0, 0, d1, e1, 0, 0, f1],
    ![0, 0, 0, 0, b3, 0, 0, d3, e3, 0, 0, f3],
    ![0, 0, 0, c2, 0, a2, b2, 0, 0, e2, 0, 0],
    ![0, 0, 0, 0, 0, 0, b1, 0, 0, e1, f1, d1],
    ![0, 0, 0, 0, 0, 0, b3, 0, 0, e3, f3, d3]]

@[expose] def atomsOf {R : Type*} [CommRing R] (ρ : ℕ → R) : ℕ → R :=
  fun k => (atomDef k).eval ρ fun _ => 0

@[expose] def matOf {R : Type*} [CommRing R] (ρ : ℕ → R) : Matrix (Fin 12) (Fin 12) R :=
  Matrix.of fun i j => (ent i j).eval ρ (atomsOf ρ)

end Elim

end CFSG.Walter.Ree.Bombieri
