module

public import CFSG.LocalAnalysis.StandardType.GGNineDepK1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGNineDepCtx {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) : Prop where
  case : GGNineDepCase p N h α r s x
  hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)
  d_ge : N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s)
  d_le : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N
  restr : GGLargeRestr r s hA

@[expose] noncomputable def ggNineQ {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (X : GGNineDepCtx h α r s x) :
    Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
  (ggLargeRho r s X.hA).range

theorem ggNineDepCtx_of_case {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) : GGNineDepCtx h α r s x := by
  obtain ⟨hA, h1, h2, hR⟩ := ggNineDep_restrict C (ggNineDep_connected C)
  exact ⟨C, hA, h1, h2, hR⟩

end CFSG.StandardType

end
