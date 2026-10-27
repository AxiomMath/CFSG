module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def RepQuad {G : Type} [Group G] (ρ : G →* LGL 2 V) (A : Subgroup G) : Prop :=
  commSpace (A.map ρ) (commSub (A.map ρ)) = ⊥

@[expose] def IsMinimalNotLE {G : Type} [Group G] (B A L : Subgroup G) : Prop :=
  A ≤ L ∧ ¬ L ≤ B ∧ ∀ L' : Subgroup G, A ≤ L' → L' ≤ L → ¬ L' ≤ B → L' = L

@[expose] def IsChiefFactor {G : Type} [Group G] (ρ : G →* LGL 2 V)
    (W₁ W₂ : Submodule (ZMod 2) V) : Prop :=
  W₂ < W₁ ∧ (∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
  ∀ U : Submodule (ZMod 2) V, W₂ ≤ U → U ≤ W₁ → (∀ g : G, ∀ u ∈ U, ρ g u ∈ U) →
    U = W₂ ∨ U = W₁

@[expose] def IsNoncentral {G : Type} [Group G] (ρ : G →* LGL 2 V)
    (W₁ W₂ : Submodule (ZMod 2) V) : Prop :=
  ∃ g : G, ∃ w ∈ W₁, ρ g w - w ∉ W₂

@[expose] def IsNatSL2Section {G : Type} [Group G] (ρ : G →* LGL 2 V) (N : Subgroup G)
    (W₁ W₂ : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  W₂ ≤ W₁ ∧ (∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : G →* SL(2, K)) (ψ : ↥W₁ →+ (Fin 2 → K)),
    Nat.card K = 2 ^ n ∧ Function.Surjective φ ∧ φ.ker = N ∧
    Function.Surjective ψ ∧ (∀ w : ↥W₁, ψ w = 0 ↔ (w : V) ∈ W₂) ∧
    ∀ (g : G) (w : ↥W₁) (hw : ρ g (w : V) ∈ W₁),
      ψ ⟨ρ g (w : V), hw⟩ = (φ g : Matrix (Fin 2) (Fin 2) K).mulVec (ψ w)

@[expose] def IsNatSzSection {G : Type} [Group G] (ρ : G →* LGL 2 V) (N : Subgroup G)
    (W₁ W₂ : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  W₂ ≤ W₁ ∧ (∀ g : G, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
  ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (φ : G →* ↥(CFSG.Blueprint.suzukiGroup a K)) (ψ : ↥W₁ →+ (Fin 4 → K)),
    1 ≤ a ∧ n = 2 * a + 1 ∧ Nat.card K = 2 ^ n ∧ Function.Surjective φ ∧
    φ.ker = N ∧ Function.Surjective ψ ∧ (∀ w : ↥W₁, ψ w = 0 ↔ (w : V) ∈ W₂) ∧
    ∀ (g : G) (w : ↥W₁) (hw : ρ g (w : V) ∈ W₁),
      ψ ⟨ρ g (w : V), hw⟩ =
        ((φ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec (ψ w)

@[expose] def IsNatSection {G : Type} [Group G] (ρ : G →* LGL 2 V) (N : Subgroup G)
    (W₁ W₂ : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  IsNatSL2Section ρ N W₁ W₂ n ∨ IsNatSzSection ρ N W₁ W₂ n

@[expose] def IsSumNatSection {G : Type} [Group G] (ρ : G →* LGL 2 V) (N : Subgroup G)
    (W₁ W₂ : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ s : Finset (Submodule (ZMod 2) V),
    (∀ U ∈ s, W₂ ≤ U ∧ U ≤ W₁ ∧ IsNatSection ρ N U W₂ n) ∧
    (s.sup id ⊔ W₂ = W₁) ∧
    ∀ U ∈ s, U ⊓ ((s.erase U).sup id ⊔ W₂) ≤ W₂

structure Setting12One {G : Type} [Group G] (ρ : G →* LGL 2 V) (B : Subgroup G)
    (Z : Submodule (ZMod 2) V) (A : Subgroup G) (n m : ℕ) : Prop where
  type : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G
  borel : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B
  stab : ∀ g : G, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z
  A_le_B : A ≤ B
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card A = 2 ^ m
  one_lt_m : 1 < m
  quad : RepQuad ρ A

instance kerIn_top_normal12 {G : Type} [Group G] (M : Subgroup G) :
    (CFSG.Quasithin.kerIn M ⊤).Normal where
  conj_mem n hn g := by
    refine CFSG.Quasithin.mem_kerIn.mpr fun b _ => ?_
    have h := (CFSG.Quasithin.mem_kerIn.mp hn) (b * g) (Subgroup.mem_top _)
    simpa [mul_assoc] using h

structure Setting12Two {G : Type} [Group G] (A M : Subgroup G) (n : ℕ) : Prop where
  A_two : IsPGroup 2 A
  A_le_M : A ≤ M
  M_ne : M ≠ ⊤
  unique_max : ∀ N : Subgroup G, A ≤ N → N ≠ ⊤ → N ≤ M
  type : CFSG.Quasithin.IsPSL 2 2 n (G ⧸ CFSG.Quasithin.kerIn M ⊤) ∨
    CFSG.Quasithin.IsSz n (G ⧸ CFSG.Quasithin.kerIn M ⊤)
  one_lt_n : 1 < n

end CFSG.LocalAnalysis.WeakClosure81
