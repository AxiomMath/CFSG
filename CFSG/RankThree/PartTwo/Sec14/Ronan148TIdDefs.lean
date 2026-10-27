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

@[expose] def HeisAct148 (X : Type) [Group X] (P : Subgroup (MulAut X)) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (F : Type) (_ : Field F) (_ : PiField π p f F) (_ : ModThree π (p ^ f))
    (φ : X ≃* projImage (slPi π 3 (p ^ f) F)) (y₁ y₂ : GL (Fin 3) F) (ζ : Fˣ),
    y₁ ∈ glPi π 3 (p ^ f) F ∧ y₂ ∈ glPi π 3 (p ^ f) F ∧
      y₁ ^ 3 ∈ StatedScalars (Fin 3) F ∧ y₂ ^ 3 ∈ StatedScalars (Fin 3) F ∧ ζ ≠ 1 ∧
      y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂ ∧
      ∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
        ((φ (σ z) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
          ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j) * (φ z : ProjGenLinGroup (Fin 3) F) *
            (ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j))⁻¹

@[expose] def L3IdentHeis : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X)
    (Q D : Subgroup (MulAut X)),
    HeisAct148 X P → IsLThreePi X → Subgroup.center X = ⊥ → ¬ Group.IsSolvable X →
    CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    (∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e → Sec4.IsoLThreePi X p e → p = 2 ∨ e ≤ 2) →
    Q ≤ (MulAut.conj : X →* MulAut X).range →
    Ronan148B.SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D →
    K₀ ≠ ⊤ → Group.IsPerfect ↥K₀ → IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) →
    Ronan148B.L3Ident148 P K₀

@[expose] def ThetaHeis148 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X),
    HeisAct148 X P → Nat.card P = 9 → Subgroup.center X = ⊥ →
    (∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀) →
    Group.IsPerfect ↥K₀ → IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) →
    aschbacherSolvableCore 3 ↥K₀ = ⊥

@[expose] def SimpleHeis148 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X)
    (Q D : Subgroup (MulAut X)),
    HeisAct148 X P → IsLThreePi X → Subgroup.center X = ⊥ → ¬ Group.IsSolvable X →
    CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    (∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e → Sec4.IsoLThreePi X p e → p = 2 ∨ e ≤ 2) →
    Q ≤ (MulAut.conj : X →* MulAut X).range →
    Ronan148B.SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D →
    K₀ ≠ ⊤ → IsSimpleGroup ↥K₀ → (∃ a b : ↥K₀, a * b ≠ b * a) →
    Ronan148B.L3Ident148 P K₀

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
