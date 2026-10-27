module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.Classical.GL3

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def basisInvolution {n : ℕ} (e : Module.Basis (Fin n) (ZMod 2) V)
    (f : Fin n → V) (hf : ∀ i, e.constr (ZMod 2) f (f i) = e i) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive (e.constr (ZMod 2) f) fun x => by
    have h : (e.constr (ZMod 2) f) ∘ₗ (e.constr (ZMod 2) f) = LinearMap.id :=
      e.ext fun i => by rw [LinearMap.comp_apply, e.constr_basis, hf, LinearMap.id_apply]
    exact LinearMap.congr_fun h x

theorem basisInvolution_apply_basis {n : ℕ} (e : Module.Basis (Fin n) (ZMod 2) V)
    (f : Fin n → V) (hf : ∀ i, e.constr (ZMod 2) f (f i) = e i) (i : Fin n) :
    basisInvolution e f hf (e i) = f i :=
  e.constr_basis (ZMod 2) f i

variable (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V) (hb : ∀ v, b v v = 0)

end CFSG.RankThree.Classical.GL3
