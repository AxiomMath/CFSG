module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.SzN31

@[expose] def gFun (p : ℕ) : ℕ := if p = 3 then 2 else if p = 5 then 4 else 6

section Frame

variable (V : Type) [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixSp (t : V ≃ₗ[ZMod 2] V) (S : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  S ⊓ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1)

@[expose] def commSp (t : V ≃ₗ[ZMod 2] V) (S : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  S.map ((t : V →ₗ[ZMod 2] V) - 1)

structure Frame (ι : Type) where
  x : ι → V ≃ₗ[ZMod 2] V
  a : ι → V ≃ₗ[ZMod 2] V
  p : ι → ℕ
  prime : ∀ i, (p i).Prime
  odd : ∀ i, p i ≠ 2
  xpow : ∀ i, x i ^ p i = 1
  asq : ∀ i, a i * a i = 1
  conj : ∀ i, a i * x i * (a i)⁻¹ = (x i)⁻¹
  xx : ∀ i j, i ≠ j → x i * x j = x j * x i
  aa : ∀ i j, i ≠ j → a i * a j = a j * a i
  xa : ∀ i j, i ≠ j → x i * a j = a j * x i

@[expose] def Adm {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} (F : Frame V ι)
    (S : Submodule (ZMod 2) V) (J : Finset ι) : Prop :=
  ∀ i ∈ J, (∀ s ∈ S, F.x i s ∈ S) ∧ (∀ s ∈ S, F.a i s ∈ S) ∧ ∃ s ∈ S, F.x i s ≠ s

end Frame

end CFSG.Quasithin.SzN31
