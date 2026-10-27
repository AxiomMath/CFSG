module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08LineStab {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (xv : V) : Set (V ≃ₗ[ZMod 3] V) :=
  {a | a ∈ R ∧ ∃ c : ZMod 3, c ≠ 0 ∧ a xv = c • xv}

@[expose] def GGQ2S08M0 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (r : V ≃ₗ[ZMod 3] V) (xv : V) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r} ∪ GGQ2S08LineStab R xv)

@[expose] def GGQ2S08CoreRO {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (r : V ≃ₗ[ZMod 3] V) (xv : V) : Prop :=
  Even N ∧ ∃ f : Fin N → V, LinearIndependent (ZMod 3) f ∧ Submodule.span (ZMod 3)
    (Set.range f) = ⊤ ∧
    xv = ∑ i, f i ∧ (∀ w ∈ W, ∃ σ : Equiv.Perm (Fin N), ∀ i, w (f i) = f (σ i)) ∧
    (∀ a, a ∈ R ↔ GGQ2S08Mono f a) ∧ (∀ a, a ∈ GGQ2S08M0 R W r xv ↔ GGQ2S08MonoEven f a)

end CFSG.StandardType

end
