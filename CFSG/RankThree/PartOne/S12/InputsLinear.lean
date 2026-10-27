module

public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.RankThree.SubgroupLists (omegaGL)
open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open Matrix

instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def ExtDickson : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup (GL (Fin 2) (ZMod p))), p ∣ Nat.card H →
    (∃ P : Sylow p H, (P : Subgroup H).Normal ∧ Nat.card P = p) ∨ StatedSL 2 (ZMod p) ≤ H

@[expose] def ExtBloomMitchell : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ {G : Subgroup (GL (Fin 3) (ZMod p))},
    IsIrreducibleMatrixRep G.subtype →
    ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ IsIrreducibleMatrixRep H.subtype ∧
      (H = StatedSL 3 (ZMod p) ∨
        (∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M) ∨
        (Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧
          (∀ g ∈ G, ∃ h ∈ H, ∃ z ∈ G, (∀ y ∈ G, z * y = y * z) ∧ g = h * z) ∧
          ∀ z ∈ H, (∀ y ∈ G, z * y = y * z) → z = 1) ∨
        (Nonempty (H ≃* GL (Fin 3) (ZMod 2)) ∧ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)) ∨
        (Group.IsPerfect H ∧ Nat.card (Subgroup.center H) = 3 ∧
          Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) ∧
          (p % 30 = 1 ∨ p % 30 = 19)) ∨
        (IsCyclic H ∧ Nat.card H ∣ p ^ 3 - 1 ∧ ¬ Nat.card H ∣ p - 1) ∨
        (Nat.card H = 27 ∧ CFSG.IsExtraspecialPGroup 3 H ∧ p % 3 = 1) ∨
        (H = G ∧ CFSG.RankThree.SubgroupLists.IsTransitiveMonomial G))

@[expose] def ExtBloomPrime : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ {G : Subgroup (GL (Fin 3) (ZMod p))},
    IsIrreducibleMatrixRep G.subtype → p ∣ Nat.card G →
    ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ IsIrreducibleMatrixRep H.subtype ∧
      Group.IsPerfect H ∧
      (H = StatedSL 3 (ZMod p) ∨
        ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M)

@[expose] def ExtJonesParshallSL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (B : Submodule (ZMod p) V) (n : ℕ), (n = 2 ∨ n = 3) →
    ∀ (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p)) (ρ : StatedSL n (ZMod p) →* (V ≃ₗ[ZMod p] V)),
    Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V →
    (∀ (y : StatedSL n (ZMod p)) (b : B), ρ y (b : V) =
      ((θ.symm (((y : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b) : B) : V)) →
    (∀ (y : StatedSL n (ZMod p)) (v : V), ρ y v - v ∈ B) →
    ∃ v : V, v ∉ B ∧ ∀ y : StatedSL n (ZMod p), ρ y v = v

@[expose] def ExtJonesParshallOmega : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → p ≠ 5 → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (B : Submodule (ZMod p) V) (M : Matrix (Fin 3) (Fin 3) (ZMod p)),
    Mᵀ = M → M.det ≠ 0 →
    ∀ (θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p)) (ρ : omegaGL M →* (V ≃ₗ[ZMod p] V)),
    Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V →
    (∀ (y : omegaGL M) (b : B), ρ y (b : V) =
      ((θ.symm (((y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ θ b) : B) : V)) →
    (∀ (y : omegaGL M) (v : V), ρ y v - v ∈ B) →
    ∃ v : V, v ∉ B ∧ ∀ y : omegaGL M, ρ y v = v

@[expose] def ExtJonesParshall : Prop :=
  ExtJonesParshallSL ∧ ExtJonesParshallOmega

@[expose] def KF126 : Prop :=
  ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 5), Mᵀ = M → M.det ≠ 0 →
    Nat.card (omegaGL M) = 60 ∧
      ∀ Λ : Subgroup (GL (Fin 3) (ZMod 5)), Λ ≤ Subgroup.normalizer (omegaGL M : Set _) →
        Group.IsPerfect Λ → Λ ≤ omegaGL M

@[expose] def IsTransvectionLin {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (t : V ≃ₗ[ZMod p] V) : Prop :=
  Module.finrank (ZMod p) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1 ∧
    (t.toLinearMap - LinearMap.id) ∘ₗ (t.toLinearMap - LinearMap.id) = 0

@[expose] def KF127 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V],
    (Module.finrank (ZMod p) V = 3 ∨ Module.finrank (ZMod p) V = 4) →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod p] V),
      (∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤) →
      CFSG.pCore p Γ = ⊥ → (∃ t ∈ Γ, IsTransvectionLin t) →
      ∀ v : V, v ≠ 0 → (¬ ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v}) →
      ∀ Λ : Subgroup (V ≃ₗ[ZMod p] V), Λ ≤ Γ →
        (∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) →
        (∀ l ∈ Λ, l v = v) → CFSG.pCore p Λ = ⊥ →
        (∀ U : Submodule (ZMod p) V, (∀ l ∈ Λ, ∀ x ∈ U, l x ∈ U) → U ≠ ⊥ → U ≠ ⊤ →
          U = Submodule.span (ZMod p) {v} ∨
            Module.finrank (ZMod p) U + 1 = Module.finrank (ZMod p) V) →
        ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a

end CFSG.RankThree.PartOne
