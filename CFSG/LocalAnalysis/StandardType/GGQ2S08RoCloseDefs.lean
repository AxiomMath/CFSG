module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08Mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (f : Fin N → V)
    (g : V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin N)) (ε : Fin N → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ i, g (f i) = ε i • f (σ i)

@[expose] def GGQ2S08MonoEven {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Fin N → V) (g : V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin N)) (ε : Fin N → ZMod 3), (∀ i, ε i ≠ 0) ∧ (∏ i, ε i = 1) ∧
    ∀ i, g (f i) = ε i • f (σ i)

@[expose] def GGQ2S08ROFrame {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (f : Fin N → M.V) : Prop :=
  LinearIndependent (ZMod 3) f ∧ Submodule.span (ZMod 3) (Set.range f) = ⊤ ∧ M.xV = ∑ i, f i ∧
    ∀ a ∈ ggAutomizer L Bs, ∃ σ : Equiv.Perm (Fin N), ∀ i, ggLin (p := 3) M.model a (f i) = f (σ i)

@[expose] def GGQ2S08ROComponents {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (f : Fin N → M.V) : Prop :=
  ∃ Q : Fin N → Subgroup G, (∀ j, Q j ≤ L) ∧
    (∀ j, LargeEvenPComponent 3 (Subgroup.centralizer
      ({x, ((Additive.toMul (M.model.symm (f j)) : ↥Bs) : G)} : Set G)) (Q j)) ∧
    (∀ j, Bs ≤ Subgroup.normalizer (Q j : Set G)) ∧
    (∀ j, 4 ∣ Nat.card ↥(ggAutomizer (Q j) Bs)) ∧ ∀ i j, i ≠ j → Q i ⊔ Q j = L

end CFSG.StandardType

end
