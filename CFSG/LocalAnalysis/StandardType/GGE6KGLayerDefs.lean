module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggRFix {L' R : Type} [Group L'] [Group R] (ψ : L' →* R) (F : Set (MulAut L')) :
    Subgroup R where
  carrier := {r | ∃ l, ψ l = r ∧ ∀ f ∈ F, ψ (f l) = ψ l}
  mul_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x * y, map_mul ψ x y, fun f hf => by rw [map_mul, map_mul, map_mul, hx f hf, hy f hf]⟩
  one_mem' := ⟨1, map_one ψ, fun f _ => by rw [map_one, map_one]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl, hx⟩
    exact ⟨x⁻¹, map_inv ψ x, fun f hf => by rw [map_inv, map_inv, map_inv, hx f hf]⟩

@[expose] def GGLayerOf {R : Type} [Group R] (X E : Subgroup R) : Prop :=
  E ≤ X ∧ (E.subgroupOf X).Normal ∧ IsQuasisimple E ∧
    ∀ P : Subgroup R, P ≤ X → ⁅P, P⁆ = P → P ≤ E

@[expose] def GGE6KGLayers (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
    (∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c →
      ∃ E : Subgroup R, GGLayerOf (ggRFix ψ {(c : MulAut L')}) E) ∧
    ∀ a b : ↥A, GGCorootOrth 3 (ggTorusAut A) a b →
      ∃ Ev Eab : Subgroup R,
        GGLayerOf (ggRFix ψ {(a : MulAut L') * (b : MulAut L')}) Ev ∧
        GGLayerOf (ggRFix ψ {(a : MulAut L'), (b : MulAut L')}) Eab ∧
        (∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
          ∃ l : L', ψ l ∈ Eab ∧ MulAut.conj l = (u : MulAut L')) ∧
        (∃ l : L', ψ l ∈ Ev ∧ MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
          MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ ≠ (a : MulAut L')) ∧
        ∀ (N : Type) [Group N] [Finite N] (π : N →* Eab), Function.Surjective π →
          π.ker ≤ Subgroup.center N → commutator N = ⊤ → IsCyclic (Subgroup.center N)

@[expose] def GGE6KGLayerInput : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6KGLayers R I

end CFSG.StandardType

end
