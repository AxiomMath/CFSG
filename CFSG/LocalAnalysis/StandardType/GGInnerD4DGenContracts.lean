module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4ComponentIdent
public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType.S2MathAs51600Contracts

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal

open scoped commutatorElement

@[expose] def OrthogonalInnerRepresentatives : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ (X : Type) [Group X], commutator X = ⊤ →
    ∀ (θ : X ⧸ Subgroup.center X ≃* ProjOrthDerived Q),
    ∀ (A : Subgroup (MulAut X)),
    IsElemAbelian 3 A →
    GGInducedInn A θ (LargeEvenInnSet (ProjOrthDerived Q)) →
    ∃ t : A →* orthDerived Q,
      Function.Injective t ∧
      (∀ a : A, MulAut.conj
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) (t a)) =
          ggInducedAut θ (a : MulAut X)) ∧
      (∀ a : A, (t a) ^ 3 = 1) ∧
      (∀ a b : A, Commute (t a) (t b)) ∧
      (∀ (a : A) (u : orthDerived Q),
        MulAut.conj
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) u) =
            ggInducedAut θ (a : MulAut X) → u = t a)

@[expose] def SupportedFixedThreeInner : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (x : V ≃ₗ[K] V),
    OddOrderIsometry Q 3 x →
    (∃ U : Submodule K (fixedSpace x), Module.finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) →
    ∀ (c : V ≃ₗ[K] V), c ∈ isometryCentralizer Q x → c ^ 3 = 1 →
    ∃ u ∈ supportedFixedDerived Q x, u ^ 3 = 1 ∧
      ∀ g ∈ supportedFixedDerived Q x,
        c * g * c⁻¹ = u * g * u⁻¹

@[expose] def OrthogonalD4ComponentInner : Prop :=
  GGLabelRigidInput →
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n n' : ℕ), 1 ≤ n → 1 ≤ n' → Nat.card K = 2 ^ n →
    ∀ (Q : QuadraticForm K V),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ (x c : orthDerived Q),
    OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) →
    c ^ 3 = 1 → Commute c x →
    ∀ (I : Subgroup (ProjOrthDerived Q)),
    CFSG.Open.IsComponentOf I (centralizerImage Q (x : V ≃ₗ[K] V)) →
    GGHasLabel (⟨.D, 4, n'⟩ : LargeEvenLabel) (I ⧸ Subgroup.center I) →
    ∃ u ∈ I, ∀ v ∈ I,
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) c) * v *
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) c)⁻¹ =
          u * v * u⁻¹

theorem liftInnerOnPerfectComponent {H C : Type*} [Group H] [Group C] {Φ : H →* C}
    (hker : Φ.ker ≤ Subgroup.center H) {Q : Subgroup H} {F : Subgroup C}
    (hQ : ⁅Q, Q⁆ = Q) (hQF : Q.map Φ = F) (τ : H →* H) {x : C} (hx : x ∈ F)
    (h : ∀ y ∈ Q, Φ (τ y) = x * Φ y * x⁻¹) :
    ∃ x' ∈ Q, ∀ y ∈ Q, τ y = x' * y * x'⁻¹ :=
  CFSG.RankThree.PartOne.S15K.exists_inner_of_map_eq_conj hker hQ hQF τ hx h

end CFSG.StandardType.S2MathAs51600Contracts

end
