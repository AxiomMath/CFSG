module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def LeafModelOn (t : ℕ) (Na Nb : Subgroup (V t ≃ₗ[F] V t)) (vx z : V t) : Prop :=
  ∃ W : GGQ2LinOn 3 (V t),
    W.toLin.parab {i | i ≠ W.a} = Na ∧
    W.toLin.parab {i | i ≠ W.b} = Nb ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span F {vx}) ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔ v ∈ Submodule.span F {z}) ∧
    ∃! c, c ≠ W.b ∧ W.cartan W.b c ≠ 0

theorem LeafModelOn.swap {t : ℕ} {Na Nb : Subgroup (V t ≃ₗ[F] V t)} {vx z : V t}
    (h : LeafModelOn t Na Nb vx z) : LeafModelOn t Nb Na z vx := by
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := h
  exact ⟨{ W with a := W.b, b := W.a, a_ne_b := W.a_ne_b.symm, a_leaf := h5 }, h2, h1, h4, h3,
    W.a_leaf⟩

@[expose] def ChainWitnessOn (t : ℕ) (Na Nb : Subgroup (V t ≃ₗ[F] V t)) (vx z : V t) : Prop :=
  ∃ W : GGQ2LinOn 3 (V t),
    W.toLin.parab {i | i ≠ W.a} = Na ∧
    W.toLin.parab {i | i ≠ W.b} = Nb ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span F {vx}) ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔ v ∈ Submodule.span F {z})

theorem LeafModelOn.chainWitnessOn {t : ℕ} {Na Nb : Subgroup (V t ≃ₗ[F] V t)} {vx z : V t}
    (h : LeafModelOn t Na Nb vx z) : ChainWitnessOn t Na Nb vx z := by
  obtain ⟨W, h1, h2, h3, h4, -⟩ := h
  exact ⟨W, h1, h2, h3, h4⟩

@[expose] def AmbientChainOn (t : ℕ) (Na Nab : Subgroup (V t ≃ₗ[F] V t)) (vx z : V t) : Prop :=
  ∃ W : GGQ2LinOn 3 (V t),
    W.toLin.parab {i | i ≠ W.a} = Na ∧
    W.toLin.simpleRefl W.a ∈ Nab ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span F {vx}) ∧
    (∀ i, i ≠ W.a → i ≠ W.b → W.root i z = 0) ∧
    W.toLin.Basis ∧ ((W.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
    ((W.cartan.submatrix (fun i : {i // i ≠ W.a} => (i : W.ι))
      (fun i : {i // i ≠ W.a} => (i : W.ι))).det : ZMod 3) ≠ 0

@[expose] def LeafModelFlip : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ e : V t, (∀ i, e i ≠ 0) → ∀ i₀ : Fin t,
    LeafModelOn t (twistedPermGroupOn t e)
      (twistedPermGroupOn t (Function.update e i₀ (-e i₀))) e (Function.update e i₀ (-e i₀))

@[expose] def LeafModelSigned : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ e : V t, (∀ i, e i ≠ 0) → ∀ i₁ : Fin t,
    LeafModelOn t (twistedPermGroupOn t e) (signedPermGroupOn t (Finset.univ.erase i₁)) e
      (Pi.single i₁ 1)

@[expose] def LeafModelEvenSigned : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ e : V t, (∀ i, e i ≠ 0) → ∀ i₁ : Fin t,
    LeafModelOn t (twistedPermGroupOn t e) (evenSignedPermGroupOn t (Finset.univ.erase i₁)) e
      (Pi.single i₁ 1)

@[expose] def AmbientChainEvenSigned : Prop :=
  ∀ t : ℕ, ∀ ht : 4 ≤ t, ∀ i₁ i₂ : Fin t, i₁ ≠ i₂ →
    ∃ (W : GGQ2LinOn 3 (V t)) (f : Fin t ≃ W.ι),
      (∀ i j, W.cartan (f i) (f j) = CartanMatrix.D t i j) ∧
      W.a = f ⟨0, by omega⟩ ∧ W.b = f ⟨1, by omega⟩ ∧
      W.toLin.parab {i | i ≠ W.a} = evenSignedPermGroupOn t (Finset.univ.erase i₁) ∧
      W.toLin.parab {i | i ≠ W.a ∧ i ≠ W.b} = evenSignedPermGroupOn t (Finset.univ \ {i₁, i₂}) ∧
      W.toLin.simpleRefl W.a = swapEquiv t i₁ i₂ ∧
      (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}) ∧
      (∀ i, i ≠ W.a → i ≠ W.b → W.root i (Pi.single i₂ 1) = 0) ∧
      W.toLin.Basis

@[expose] def NbrChainSigned : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ i : Fin t, ∃ (W : GGQ2LinOn 3 (V t)) (f : Fin (t - 1) ≃ W.ι),
    (∀ a b, W.cartan (f a) (f b) = CartanMatrix.B (t - 1) a b) ∧
    W.toLin.weyl = signedPermGroupOn t (Finset.univ.erase i) ∧
    ∀ v, (∀ j, W.root j v = 0) ↔ v ∈ Submodule.span F {Pi.single i 1}

@[expose] def NbrChainEvenSigned : Prop :=
  ∀ t : ℕ, 5 ≤ t → ∀ i : Fin t, ∃ (W : GGQ2LinOn 3 (V t)) (f : Fin (t - 1) ≃ W.ι),
    (∀ a b, W.cartan (f a) (f b) = CartanMatrix.D (t - 1) a b) ∧
    W.toLin.weyl = evenSignedPermGroupOn t (Finset.univ.erase i) ∧
    ∀ v, (∀ j, W.root j v = 0) ↔ v ∈ Submodule.span F {Pi.single i 1}

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
