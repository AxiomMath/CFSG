module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
public import CFSG.ClassicalInvolution.Phan.Defs

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

@[expose] def reflFixedCoord (p r : ℕ) (i j : Fin r) : Subgroup (Fin r → Multiplicative (ZMod p)) :=
  MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i /
    Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)

@[expose] def reflFixedCoordPos (p r : ℕ) (i j : Fin r) : Subgroup (Fin r → Multiplicative (ZMod p)) :=
  MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i *
    Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)

@[expose] def TBJOmData.reflFixed {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (i j : Fin r) : Subgroup (V ≃ₗ[K] V) :=
  (reflFixedCoord p r i j).map Δ.τ

@[expose] def TBJOmData.reflFixedPos {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (i j : Fin r) : Subgroup (V ≃ₗ[K] V) :=
  (reflFixedCoordPos p r i j).map Δ.τ

@[expose] def TBJOmData.rankOne {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (i j : Fin r) : Subgroup (V ≃ₗ[K] V) :=
  CFSG.StandardType.ggOTwoPrime
    (Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q)

@[expose] def TBJOmData.rankOnePos {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (i j : Fin r) : Subgroup (V ≃ₗ[K] V) :=
  CFSG.StandardType.ggOTwoPrime
    (Subgroup.centralizer (Δ.reflFixedPos i j : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q)

@[expose] def TBJOmData.RankOneModel {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) : Prop :=
  ∀ i j : Fin r, i ≠ j →
    (∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      Function.Injective θ ∧ θ.range = Δ.rankOne i j ∧
        ∀ g ∈ θ.range, ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, g u = u) ∧
    ∀ x ∈ Δ.rankOne i j, ∀ y ∈ Δ.rankOnePos i j, x * y = y * x

@[expose] def TBJOmData.PairModel {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (Δ : TBJOmData Q p A r) (f : ℕ) (K' : Type) [Field K'] [Finite K'] [CharP K' 2] : Prop :=
  ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∃ W : Subgroup (V ≃ₗ[K] V),
    UnitaryBlockStandardPair K' 2 f W (Δ.rankOne i j) (Δ.rankOne j k)

end OrthTorus

end CFSG.StandardType

end
