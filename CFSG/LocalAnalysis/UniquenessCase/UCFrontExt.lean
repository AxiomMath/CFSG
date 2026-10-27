module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F05
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def calP (ρ : Representation (ZMod 2) G V) : Set (Subgroup G) :=
  {A | A ≠ ⊥ ∧ IsElemAbelian 2 A ∧ IsBestOffender ρ A}

@[expose] def lgConj (L : Subgroup G) : Subgroup G :=
  ⨆ g : G, L.map (MulAut.conj g).toMonoidHom

@[expose] def SecNat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G) (A B : Submodule (ZMod 2) V)
    (H' : Subgroup (GL ι K)) : Prop :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ A ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ B ∧ B ≤ A ∧
    ∃ (φ : ↥H₁ ≃* ↥H') (ψ : V →+ (ι → K)),
      (∀ x ∈ B, ψ x = 0) ∧ (∀ x ∈ A, ψ x = 0 → x ∈ B) ∧ (∀ y : ι → K, ∃ x ∈ A, ψ x = y) ∧
      ∀ (h : ↥H₁) (x : V), x ∈ A →
        ψ (ρ (h : G) x) = ((((φ h : ↥H') : GL ι K) : Matrix ι ι K)) *ᵥ ψ x

@[expose] def SecNatS5 (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) : Prop :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ A ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ B ∧ B ≤ A ∧
    ∃ (φ : ↥H₁ ≃* Equiv.Perm (Fin 5)) (ψ : V →+ (Fin 5 → ZMod 2)),
      (∀ x ∈ B, ψ x = 0) ∧ (∀ x ∈ A, ψ x = 0 → x ∈ B) ∧ (∀ x ∈ A, ∑ i, ψ x i = 0) ∧
      (∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → ∃ x ∈ A, ψ x = y) ∧
      ∀ (h : ↥H₁) (x : V), x ∈ A → ψ (ρ (h : G) x) = fun i => ψ x ((φ h).symm i)

@[expose] def SecIrr (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) (r : ℕ) : Prop :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ A ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ B ∧ B ≤ A ∧ Nat.card A = 2 ^ r * Nat.card B ∧
    ∀ C : Submodule (ZMod 2) V, B ≤ C → C ≤ A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H₁ C → C = B ∨ C = A

@[expose] def SecSum (P : Submodule (ZMod 2) V → Submodule (ZMod 2) V → Prop) (m : ℕ)
    (A B : Submodule (ZMod 2) V) : Prop :=
  ∃ Ai : Fin m → Submodule (ZMod 2) V, (∀ i, B ≤ Ai i ∧ Ai i ≤ A ∧ P (Ai i) B) ∧
    (⨆ i, Ai i) = A ∧ ∀ i, Ai i ⊓ (⨆ j ∈ {j | j ≠ i}, Ai j) ≤ B

@[expose] def NatL2 (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    SecNat ρ H₁ A B (StatedSL 2 F)

@[expose] def NatL3 (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) : Prop :=
  SecNat ρ H₁ A B (StatedSL 3 (ZMod 2))

@[expose] def NatOmegaMinus4 (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) (m : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      SecNat ρ H₁ A B (StatedOmega (StatedQuadMinus 2 F b c))

@[expose] def NatOmegaPlus4 (ρ : Representation (ZMod 2) G V) (H₁ : Subgroup G)
    (A B : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    SecNat ρ H₁ A B (StatedOmega (StatedQuadPlus 2 F))

@[expose] def Case147 (L : Subgroup G) (n : ℕ) : Prop :=
  (1 < n ∧ Odd n ∧ IsSp4 ↥(lgConj L) n ∧ ∃ g : G, ActsNontrivOnDiagramIn (lgConj L) g) ∨
  IsSU3 ↥(lgConj L) n ∨
  (((2 < n ∧ (IsL2 ↥L n ∨ IsSz ↥L n)) ∨ (IsJ1 ↥L ∧ n = 3)) ∧ numConj L ≤ 2)

@[expose] def K147 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    ρ.IsIrreducible → ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, Case147 L n →
    mGV ρ ≤ n + 1 →
      ((∀ g : G, g ∉ normalizer (L : Set G) →
          commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
        (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
          (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8))) ∨
      NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n

@[expose] def CompShape148 (L : Subgroup G) : Prop :=
  (∃ n : ℕ, IsSp4 ↥L n ∧ ∃ g : G, ActsNontrivOnDiagramIn L g) ∨ (∃ n : ℕ, IsSU3 ↥L n ∨ IsL2 ↥L n ∨ IsSz ↥L n) ∨
    (∃ p : ℕ, p.Prime ∧ IsL2Odd ↥L p) ∨ IsJ1 ↥L

@[expose] def IsInternalDirect {m : ℕ} (H : Subgroup G) (Hs : Fin m → Subgroup G) : Prop :=
  (⨆ i, Hs i) = H ∧ (∀ i j, i ≠ j → ∀ x ∈ Hs i, ∀ y ∈ Hs j, x * y = y * x) ∧
    ∀ i, Hs i ⊓ (⨆ j ∈ {j | j ≠ i}, Hs j) = ⊥

@[expose] def Shape148 (ρ : Representation (ZMod 2) G V) (Hi : Subgroup G)
    (Ui C : Submodule (ZMod 2) V) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ NatL2 ρ Hi Ui (Ui ⊓ C) n) ∨
  NatL3 ρ Hi Ui (Ui ⊓ C) ∨ SecSum (fun A B => NatL3 ρ Hi A B) 2 Ui (Ui ⊓ C) ∨
  SecNatS5 ρ Hi Ui (Ui ⊓ C)

@[expose] def hP (ρ : Representation (ZMod 2) G V) : Subgroup G :=
  ⨆ A ∈ calP ρ, A

@[expose] def uP (ρ : Representation (ZMod 2) G V) : Submodule (ZMod 2) V :=
  commOn ρ (hP ρ) ⊤

@[expose] def cUP (ρ : Representation (ZMod 2) G V) : Submodule (ZMod 2) V :=
  uP ρ ⊓ fixSub ρ (hP ρ)

@[expose] def IsDirectSumMod {m : ℕ} (U C : Submodule (ZMod 2) V)
    (Ui : Fin m → Submodule (ZMod 2) V) : Prop :=
  ((⨆ i, Ui i) ⊔ C = U) ∧
    ∀ i, (Ui i ⊔ C) ⊓ ((⨆ j ∈ {j | j ≠ i}, Ui j) ⊔ C) ≤ C

@[expose] def K148 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    (∀ L : Subgroup G, IsComponentOf L ⊤ → CompShape148 L) → hP ρ ≠ ⊥ →
      ∃ (m : ℕ) (Hs : Fin m → Subgroup G),
        IsInternalDirect (hP ρ) Hs ∧
        IsDirectSumMod (uP ρ) (cUP ρ) (fun i => commOn ρ (Hs i) (uP ρ)) ∧
        ∀ i, Shape148 ρ (Hs i) (commOn ρ (Hs i) (uP ρ)) (cUP ρ)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
