module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative NbrOrth

@[expose] def GGTorusOrthFrameSC (p : ℕ) (R : Type) [Group R] (ℓ : ℕ) : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      ((k = ℓ ∧ (∀ i j : Fin k, i ≠ j → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
          ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
            ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
              ∏ i, ε i = 1 ∧
              ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∨
        (k + 1 = ℓ ∧ (∀ i : Fin k, ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
          ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
            ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
              ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)))

end CFSG.StandardType

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

@[expose] def DCoordModel {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) (n : ℕ)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) : Prop :=
  ∀ a : MulAut ↥Bs, a ∈ ggAutomizer X Bs ↔
    ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
      ∀ (f : Fin (n + 1) → Multiplicative (ZMod p)) (i : Fin (n + 1)),
        Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)

@[expose] def DFrameOmegaLeaf : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 → ∀ ℓ : ℕ, Module.finrank F V = 2 * ℓ → 4 ≤ ℓ →
      GGTorusOrthFrameSC p ↥(CFSG.RankThree.Classical2.orthDerived Q) ℓ

@[expose] def DSideCoordLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs X : Subgroup G) (z : G) (hz : z ∈ Bs),
    p = 3 → GGBstar p B Bs → GGInnerDiagOn Bs X →
    (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
      (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 6 ≤ lab.rank) →
    z ≠ 1 → Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z → p ^ 4 ≤ Nat.card Bs →
    ∃ (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨z, hz⟩ ∧
      ((6 ≤ n ∧ DCoordModel p Bs X n τ) ∨ (5 ≤ n ∧ C2CoordModel p Bs X n τ))

end CFSG.StandardType.HdRo7D
