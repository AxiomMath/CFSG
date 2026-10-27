module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3IdentDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup)

@[expose] def SubHeis148 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X)
    (Q D : Subgroup (MulAut X)) (π : Bool) (p f : ℕ) [Fact p.Prime] (F : Type) [Field F],
    PiField π p f F → ModThree π (p ^ f) →
    ∀ (φ : X ≃* projImage (slPi π 3 (p ^ f) F)) (y₁ y₂ : GL (Fin 3) F) (ζ : Fˣ),
    y₁ ∈ glPi π 3 (p ^ f) F → y₂ ∈ glPi π 3 (p ^ f) F →
    y₁ ^ 3 ∈ StatedScalars (Fin 3) F → y₂ ^ 3 ∈ StatedScalars (Fin 3) F → ζ ≠ 1 →
    y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂ →
    (∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
      ((φ (σ z) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j) * (φ z : ProjGenLinGroup (Fin 3) F) *
          (ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j))⁻¹) →
    Subgroup.center X = ⊥ → CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    Q ≤ (MulAut.conj : X →* MulAut X).range →
    Ronan148B.SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D →
    K₀ ≠ ⊤ → IsSimpleGroup ↥K₀ →
    ∀ f₁ : ℕ, 1 ≤ f₁ → (p = 2 ∨ f₁ ≤ 2) → IsLThreeEpsAt ↥K₀ p f₁ →
    Ronan148B.L3Ident148 P K₀

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
