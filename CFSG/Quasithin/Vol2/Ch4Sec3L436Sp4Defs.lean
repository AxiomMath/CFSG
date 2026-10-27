module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def Sp4MultTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → CFSG.Open.IsQuasisimple X →
    IsPSp4 2 n (X ⧸ Subgroup.center X) → Subgroup.center X = ⊥

namespace L436

@[expose] noncomputable def uT (F : Type) [Field F] (t : F) :
    CFSG.Assembly.LowTwoRank.StatedSL 2 F :=
  ⟨⟨!![1, t; 0, 1], !![1, -t; 0, 1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩

variable {G : Type} [Group G]

@[expose] def sp4C (P V : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer (perfectCore P : Set G)

@[expose] def sp4Z (P S V : Subgroup G) : Subgroup G :=
  ⁅V ⊓ Subgroup.centralizer (S : Set G), perfectCore P ⊓ Subgroup.normalizer (S : Set G)⁆

@[expose] def sp4K₂ (K P S V : Subgroup G) : Subgroup G :=
  perfectCore (K ⊓ Subgroup.normalizer (sp4Z P S V : Set G))

@[expose] def sp4Q₁ (K P S V : Subgroup G) : Subgroup G :=
  pCoreOf 2 (sp4K₂ K P S V)

@[expose] def Sp4Torus (n : ℕ) (K P C Z K₂ Q₁ : Subgroup G) : Prop :=
  ∃ Y₁ Y₂ : Subgroup G, Y₁ ≤ K ⊓ Subgroup.normalizer (Z : Set G) ∧ Y₁ ≤ P ∧ IsCyclic ↥Y₁ ∧
    Nat.card ↥Y₁ = 2 ^ n - 1 ∧ (∀ y ∈ Y₁, ∀ z ∈ Z, y * z * y⁻¹ = z → y = 1 ∨ z = 1) ∧
    (∀ y ∈ Y₁, ∀ k ∈ K₂, y * k * y⁻¹ * k⁻¹ ∈ Q₁) ∧
    K ⊓ Subgroup.normalizer (Z : Set G) = Y₁ ⊔ K₂ ∧ Y₂ ≤ K₂ ∧ IsCyclic ↥Y₂ ∧
    Nat.card ↥Y₂ = 2 ^ n - 1 ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧
    Y₁ ⊔ Y₂ ≤ Subgroup.normalizer (C : Set G) ∧
    ∀ c ∈ C, ∀ c' ∈ C, c ≠ 1 → c' ≠ 1 → ∃ y ∈ Y₁ ⊔ Y₂, y * c * y⁻¹ = c'

end L436

open L436

variable {G : Type} [Group G]

structure Sp4ParConcl (n : ℕ) (K P S V : Subgroup G) : Prop where
  V_eq : V = pCoreOf 2 (perfectCore P)
  V_sq : ∀ v ∈ V, v ^ 2 = 1
  card_V : Nat.card ↥V = 2 ^ (3 * n)
  comm_V : ⁅V, perfectCore P⁆ = V
  card_C : Nat.card ↥(sp4C P V) = 2 ^ n
  S_le : S ≤ perfectCore P
  S_syl : IsSylowTwoOf S K
  card_Z : Nat.card ↥(sp4Z P S V) = 2 ^ n
  C_inf_Z : sp4C P V ⊓ sp4Z P S V = ⊥
  cent_S : V ⊓ Subgroup.centralizer (S : Set G) = sp4C P V ⊔ sp4Z P S V
  K₂_le : sp4K₂ K P S V ≤ Subgroup.centralizer (sp4Z P S V : Set G)
  sup_eq : perfectCore P ⊔ sp4K₂ K P S V = K
  V_le_K₂ : V ≤ sp4K₂ K P S V
  K₂_closure : conjClosure V (sp4K₂ K P S V) = sp4K₂ K P S V
  psl : IsPSL 2 2 n (ModO2 (sp4K₂ K P S V))
  natural : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    IsNaturalSection (sp4K₂ K P S V) (sp4Q₁ K P S V) (sp4Z P S V)
      (CFSG.pCore 2 ↥(sp4K₂ K P S V)) (CFSG.Assembly.LowTwoRank.StatedSL 2 F)
  Q₁_closure : conjClosure (sp4C P V) (sp4K₂ K P S V) = sp4Q₁ K P S V
  card_Q₁ : Nat.card ↥(sp4Q₁ K P S V) = 2 ^ (3 * n)
  Q₁_cent : sp4Q₁ K P S V ⊓ Subgroup.centralizer (sp4K₂ K P S V : Set G) = sp4Z P S V
  S_eq : S = V ⊔ sp4Q₁ K P S V
  V_inf_Q₁ : V ⊓ sp4Q₁ K P S V = sp4C P V ⊔ sp4Z P S V
  V_cent_Q₁ : V ⊓ Subgroup.centralizer (sp4Q₁ K P S V : Set G) = V ⊓ sp4Q₁ K P S V
  Q₁_cent_V : sp4Q₁ K P S V ⊓ Subgroup.centralizer (V : Set G) = V ⊓ sp4Q₁ K P S V
  index_V : (V ⊓ sp4Q₁ K P S V).relIndex V = 2 ^ n
  index_Q₁ : (V ⊓ sp4Q₁ K P S V).relIndex (sp4Q₁ K P S V) = 2 ^ n
  torus : Sp4Torus n K P (sp4C P V) (sp4Z P S V) (sp4K₂ K P S V) (sp4Q₁ K P S V)
  coord : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ (α : ↥(perfectCore P) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))
      (β : ↥V →* Multiplicative (Fin 2 → F)),
      Function.Surjective α ∧ (∀ ℓ, α ℓ = 1 ↔ (ℓ : G) ∈ V) ∧ Function.Surjective β ∧
      (∀ v, β v = 1 ↔ (v : G) ∈ sp4C P V) ∧
      (∀ (a : ↥(perfectCore P)) (u v : ↥V), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) ∧
      (∀ ℓ : ↥(perfectCore P), (ℓ : G) ∈ S ↔ ∃ t : F, α ℓ = L436.uT F t) ∧
      (∀ v : ↥V, (v : G) ∈ sp4C P V ⊔ sp4Z P S V ↔ Multiplicative.toAdd (β v) 1 = 0)

@[expose] def Sp4ParabolicFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (K P S V : Subgroup G), 2 ≤ n →
    IsPSp4 2 n ↥K → IsMaxParabolic2 K P → IsSylowTwoOf S P →
    V ≤ pCoreOf 2 (perfectCore P) → (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) →
    perfectCore P ≤ Subgroup.normalizer (V : Set G) →
    ¬ perfectCore P ≤ Subgroup.centralizer (V : Set G) →
    Sp4ParConcl n K P S V

end CFSG.Quasithin.H13.Ch4
