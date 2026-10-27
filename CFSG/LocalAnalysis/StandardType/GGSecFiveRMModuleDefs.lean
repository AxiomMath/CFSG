module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType

section Module

@[expose] def ggLinMove
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (a : V ≃ₗ[ZMod p] V) : Submodule (ZMod p) V :=
  LinearMap.range (a.toLinearMap - LinearMap.id)

@[expose] def GGLinRefl
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) : Prop :=
  r * r = 1 ∧ Module.finrank (ZMod p) (ggLinMove r) = 1

@[expose] def ggLinCom
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Set (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V :=
  ⨆ a ∈ A, ggLinMove a

@[expose] def ggLinFix
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Set (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V where
  carrier := {v | ∀ a ∈ A, a v = v}
  add_mem' hv hw a ha := by rw [map_add, hv a ha, hw a ha]
  zero_mem' a _ := map_zero a
  smul_mem' c v hv a ha := by rw [map_smul, hv a ha]

@[expose] def GGLinAdj
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r s : V ≃ₗ[ZMod p] V) : Prop :=
  (∃ v ∈ ggLinMove s, r v ≠ v) ∧ ∃ v ∈ ggLinMove r, s v ≠ v

end Module

end CFSG.StandardType

end
