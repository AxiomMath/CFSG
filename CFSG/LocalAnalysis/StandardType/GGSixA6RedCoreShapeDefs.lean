module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSU

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

@[expose] def HasCoreLie {G : Type} [Group G] (U : Subgroup G) : Prop :=
  ∃ S : Subgroup G, S ≤ U ∧ (∀ u ∈ U, ∀ s ∈ S, u * s * u⁻¹ ∈ S) ∧
    (∃ k, LayerFacts.ggDer U k ≤ S) ∧
    (S = ⊥ ∨ (CFSG.IsQuasisimple S ∧
      (∀ z ∈ S, (∀ y ∈ S, z * y = y * z) → z ^ 2 = 1 → z = 1) ∧ GGA6CharTwoLie ↥S))

@[expose] def HermCoreInputLie : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c) →
      HasCoreLie (matUnitary hT)

@[expose] def AltCoreInputLie : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c) → (∃ y, y + T y = 1) →
      4 ≤ Nat.card D → HasCoreLie (matUnitary hT)


end CFSG.StandardType.A6Red.CoreShape
