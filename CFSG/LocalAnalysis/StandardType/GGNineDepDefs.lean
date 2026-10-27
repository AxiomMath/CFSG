module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure GGNineLinHyp (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) :
    Prop where
  p_ne_two : p ≠ 2
  N_ge : 5 ≤ N
  p_dvd : p ∣ N
  dim_le : Module.finrank (ZMod p) V ≤ N
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  refl_form : ∀ i v, r i v = v - α i v • h i
  finT : Finite T
  s_refl : ∀ k, GGLinRefl (s k)
  conn : (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected
  x_ne : x ≠ 0
  fix_s : ggLinFix (Set.range s) = Submodule.span (ZMod p) {x}
  x_not_fix : x ∉ ggLinFix (Set.range r)
  no_transv : ∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
    ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)

structure GGNineDepCase (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) :
    Prop where
  lin : GGNineLinHyp p N h α r s x
  dep : ¬ LinearIndependent (ZMod p) h
  stab : Nat.card ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) ≤
    6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s))
  two : 2 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r))
  weylL : ∃ M : CoxeterMatrix (Fin (N - 1)), GGIsWeylMatrix M ∧
    Nonempty (M.Group ≃* ↥(Subgroup.closure (Set.range s)))

end CFSG.StandardType

end
