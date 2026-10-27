module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1

public section

namespace CFSG.KC.GH74Tab

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def cfSig (n : ℕ) [NeZero n] : List (Perm (Fin n)) :=
  (permsOfList (List.finRange n)).filter fun σ => decide (σ * (vStdE1 n).1 = (vStdE1 n).1 * σ)

@[expose] def cfD : List (Perm (Fin 4)) :=
  (permsOfList (List.finRange 4)).filter fun d => decide (d * x4 = x4 * d)

@[expose] def cfF (n : ℕ) [NeZero n] : List (Amb n) :=
  (cfSig n).flatMap fun σ => (cfD.filter fun d => decide (sign σ = sign d)).map fun d => (σ, d)

@[expose] def cfKs {n : ℕ} [NeZero n] (T : Tab n) (R : List (Amb n)) : List (List ℕ) :=
  (List.finRange 64).flatMap fun i => R.map fun r => keyA n (T.el.get i * r)

@[expose] def cfCovF {n : ℕ} [NeZero n] (T : Tab n) (R : List (Amb n)) : Bool :=
  let ks := cfKs T R
  (cfF n).all fun g => decide (keyA n g ∈ ks)

end CFSG.KC.GH74Tab

end
