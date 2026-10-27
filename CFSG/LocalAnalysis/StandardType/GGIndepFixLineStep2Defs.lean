module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGFixLineHyp (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Type} (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (s : ι → (V ≃ₗ[ZMod p] V)) (x : V) : Prop where
  odd : p ≠ 2
  five_le : 5 ≤ N
  dvd : p ∣ N
  dim_le : Module.finrank (ZMod p) V ≤ N
  finite_family : Finite ι
  indep : LinearIndependent (ZMod p) h
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  r_form : ∀ i v, r i v = v - α i v • h i
  s_refl : ∀ i, GGLinRefl (s i)
  conn : (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected
  x_ne : x ≠ 0
  fix_H : ggLinFix (Set.range s) = Submodule.span (ZMod p) {x}
  x_not_fix : x ∉ ggLinFix (Set.range r)
  no_transvection : ∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
    ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)

@[expose] noncomputable def ggFixLineT {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (s : ι → (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V :=
  (⨆ i, ggLinMove (r i)) ⊔ ⨆ k, ggLinMove (s k)

@[expose] def ggLinStab {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (T : Submodule (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | (∀ v ∈ T, g v ∈ T) ∧ ∀ v ∈ T, g.symm v ∈ T}
  mul_mem' := fun {a b} ha hb =>
    ⟨fun v hv => ha.1 _ (hb.1 v hv), fun v hv => hb.2 _ (ha.2 v hv)⟩
  one_mem' := ⟨fun v hv => hv, fun v hv => hv⟩
  inv_mem' := fun {a} ha => ⟨ha.2, ha.1⟩

lemma ggLinStab_map {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {T : Submodule (ZMod p) V} (g : ↥(ggLinStab T)) :
    T.map ((g.1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = T := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact g.2.1 v hv
  · intro v hv
    exact ⟨g.1.symm v, g.2.2 v hv, by simp⟩

@[expose] noncomputable def ggLinRestrictHom {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) :
    ↥(ggLinStab T) →* (↥T ≃ₗ[ZMod p] ↥T) where
  toFun g := LinearEquiv.ofSubmodules g.1 T T (ggLinStab_map g)
  map_one' := by
    ext v
    rfl
  map_mul' a b := by
    ext v
    rfl

end CFSG.StandardType

end
