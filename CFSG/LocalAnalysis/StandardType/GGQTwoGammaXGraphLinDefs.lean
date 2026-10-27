module

public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatumTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2GraphLinCore (D : GGQ2WDatum 3) : Prop :=
  ∀ xV : D.V, xV ≠ 0 →
    (∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {xV}) →
    LinearIndependent (ZMod 3) D.coroot → xV ∉ D.corootSpan →
    D.corootSpan ⊔ Submodule.span (ZMod 3) {xV} = ⊤ →
    ∀ E : Submodule (ZMod 3) D.V, xV ∈ E → Module.finrank (ZMod 3) E = 2 →
    ∀ A : Subgroup (D.V ≃ₗ[ZMod 3] D.V), (∀ a ∈ A, ∀ v ∈ E, a v = v) → TransvectionFree A →
      4 ∣ Nat.card A → (∃ v : D.V, (∀ a ∈ A, a v = v) ∧ v ∉ E) →
      (∀ t ∈ D.weyl, IsReflLin t → (∀ v ∈ E, t v = v) →
        t ∈ A ∨ ∀ a ∈ A, t * a = a * t) →
      ∀ T : D.V ≃ₗ[ZMod 3] D.V, T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V)) →
        ∃ w ∈ D.weyl, ∀ v ∈ E, T (w v) ∈ E

@[expose] def GGQ2GraphCoreAll : Prop :=
  ∀ (D : GGQ2WDatum 3) {lab : LargeEvenLabel}, GGQ2TBLabel lab → (lab.tag = .D ∨ lab.tag = .F4) →
    GGQ2LabelWeyl lab D.coxeter → GGQ2GraphLinCore D

@[expose] def GGQ2KillFamily {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {ι₀ : Type}
    (h : ι₀ → U) (α : ι₀ → Module.Dual (ZMod 3) U) (d : U) : Prop :=
  ∃ (ι : Type) (_ : Nonempty ι) (c : ι → U) (f : ι → Module.Dual (ZMod 3) U)
      (hfc : ∀ i, f i (c i) = 2),
    (∀ i, Module.reflection (hfc i) ∈ ggQ2WeylOf h α) ∧ (∀ i, f i d = 0) ∧
    (∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ) ∧
    (∀ u : U, (∀ i, f i u = 0) → u ∈ Submodule.span (ZMod 3) {d}) ∧
    (Submodule.span (ZMod 3) (Set.range c) ⊔ Submodule.span (ZMod 3) {d} = ⊤ ∨
      (d ∈ Submodule.span (ZMod 3) (Set.range c) ∧
        Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) + 1 =
          Module.finrank (ZMod 3) U))

@[expose] def GGQ2LineCrit {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {ι₀ : Type}
    (h : ι₀ → U) (α : ι₀ → Module.Dual (ZMod 3) U) (d : U) : Prop :=
  ∀ T : U ≃ₗ[ZMod 3] U, T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
    ∃ u ∈ ggQ2WeylOf h α, T (u d) ∈ Submodule.span (ZMod 3) {d}

@[expose] def GGQ2GraphAbsCore (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    ∀ (α : Fin n → Module.Dual (ZMod 3) U), (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ d : U, d ≠ 0 → GGQ2KillFamily h α d ∨ GGQ2LineCrit h α d

end CFSG.StandardType

end
