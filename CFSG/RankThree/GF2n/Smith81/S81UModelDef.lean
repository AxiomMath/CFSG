module

public import CFSG.RankThree.GF2n.Smith81.S81U6Pure

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)

@[expose] def Cw (t : SUid σ 6) : Set (Wform σ) := {w | Wact σ t w = w}

@[expose] def Rw (t : SUid σ 6) : Set (Wform σ) := {r | ∃ w, r = Wact σ t w - w}

@[expose] def Gcent (t : SUid σ 6) : Set (SUid σ 6) := {g | g * t = t * g}

structure UInvolModel12 (t : SUid σ 6) : Prop where
  covW : ∀ w : Wform σ,
    w ∈ AddSubgroup.closure {v | ∃ g ∈ Gcent σ t, ∃ w' : Wform σ, v = Wact σ g w' - w'}
  covC : ∀ c ∈ Cw σ t, ∃ r ∈ Rw σ t, c - r ∈
    AddSubgroup.closure {v | ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'}
  P3 : ∃ U : Set (SUid σ 6), (∀ u ∈ U, u ∈ Gcent σ t) ∧
    (∀ u ∈ U, ∀ c ∈ Cw σ t, Wact σ u c - c ∈ Rw σ t) ∧
    ∀ c ∈ Cw σ t, (∀ u ∈ U, Wact σ u c = c) → c ∈ Rw σ t
  P2 : ∀ S : AddSubgroup (Wform σ), S ≠ ⊥ → (∀ s ∈ S, s ∈ Rw σ t) →
    (∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ S, Wact σ ⁅a, b⁆ s ∈ S) →
    ∃ p ∈ S, p ≠ 0 ∧ (p : Cube F) ∈ RootPt σ

structure UInvolModel3 (t : SUid σ 6) : Prop where
  CR : ∀ c ∈ Cw σ t, c ∈ Rw σ t
  beta_ne : ∃ p₁ p₂ : Wform σ, (p₁ : Cube F) ∈ RootPt σ ∧ (p₂ : Cube F) ∈ RootPt σ ∧
    p₁ + p₂ ∈ Rw σ t ∧ beta F (p₁ : Cube F) (p₂ : Cube F) ≠ 0

end CFSG.RankThree.GF2n.Smith81.U6Cube

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

@[expose] def U6InvolFactsStatement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (_ : Nat.card F = (2 ^ f) ^ 2)
    (_ : 4 ≤ 2 ^ f) (t : SUid (unitaryInvolution F 2 f) 6),
    t * t = 1 → t ≠ 1 →
      UInvolModel12 (unitaryInvolution F 2 f) t ∨ UInvolModel3 (unitaryInvolution F 2 f) t

@[expose] def U6InvariantFormStatement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (_ : Nat.card F = (2 ^ f) ^ 2)
    (B' : Wform (unitaryInvolution F 2 f) →ₗ[Fσ (unitaryInvolution F 2 f)]
      Wform (unitaryInvolution F 2 f) →ₗ[Fσ (unitaryInvolution F 2 f)] Fσ (unitaryInvolution F 2 f)),
    (∀ (g : SUid (unitaryInvolution F 2 f) 6) (u v : Wform (unitaryInvolution F 2 f)),
      B' (Wact (unitaryInvolution F 2 f) g u) (Wact (unitaryInvolution F 2 f) g v) = B' u v) →
    ∃ lam : F, ∀ u v : Wform (unitaryInvolution F 2 f),
      ((B' u v : Fσ (unitaryInvolution F 2 f)) : F) = lam * beta F (u : Cube F) (v : Cube F)

@[expose] def U6RootTransStatement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (_ : Nat.card F = (2 ^ f) ^ 2)
    (ξ : Cube F), ξ ∈ RootPt (unitaryInvolution F 2 f) →
      ∃ (g : SUid (unitaryInvolution F 2 f) 6) (c : F), c ≠ 0 ∧ unitaryInvolution F 2 f c = c ∧
        ξ = c • rho F (g : GL (Fin 6) F) (pt0 F)

end CFSG.RankThree.GF2n.Smith81
