module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsXi (T X : Subgroup G) : Prop :=
  X = oTwoUpper X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧ pCoreOf 2 (X ⊔ T) ≠ ⊥ ∧
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) ∧
      ((pCoreOf 2 X).relIndex X = p ^ 2 ∨
        ((pCoreOf 2 X).relIndex X = p ^ 3 ∧ ¬ ⁅X, X⁆ ≤ pCoreOf 2 X)) ∧
      ∀ Y : Subgroup G, ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Y → Y ≤ X →
        T ≤ Subgroup.normalizer (Y : Set G) → Y = ⁅X, X⁆ ⊔ pCoreOf 2 X ∨ Y = X

@[expose] def IsXiStar (T X : Subgroup G) : Prop :=
  IsXi T X ∧ ∀ L : Subgroup G, quasithinIsLocal T L → IsQuasisimple (L ⧸ pCore 2 L) →
    ¬ X ⊔ T ≤ L ⊔ T

@[expose] def IsXiF (T X : Subgroup G) : Prop := IsXi T X ∧ IsXf X

@[expose] def IsXiStarF (T X : Subgroup G) : Prop := IsXiStar T X ∧ IsXf X

@[expose] def sectionCentralizer (X K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧ g ∈ Subgroup.normalizer (K : Set G) ∧
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ K}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgX, hgK, hg⟩ ⟨hhX, hhK, hh⟩
    refine ⟨Subgroup.mul_mem _ hgX hhX, Subgroup.mul_mem _ hgK hhK, fun x hx => ?_⟩
    have h1 : g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hgK _).mp (hh x hx)
    have h2 := K.mul_mem h1 (hg x hx)
    convert h2 using 1
    group
  inv_mem' := by
    rintro g ⟨hgX, hgK, hg⟩
    refine ⟨Subgroup.inv_mem _ hgX, Subgroup.inv_mem _ hgK, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgX) x).mp hx
      simpa using this
    have h1 := K.inv_mem (hg _ hx')
    convert h1 using 1
    group

@[expose] def IsXiMinus (T X : Subgroup G) : Prop :=
  IsXi T X ∧
    ((∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 3) ∨
      ((∀ q : ℕ, q.Prime → q ∣ (pCoreOf 2 X).relIndex X → q = 5) ∧
        ∀ q : ℕ, q.Prime →
          q ∣ (sectionCentralizer X (pCoreOf 2 X)).relIndex
            (Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G)) →
          q = 2 ∨ q = 5))

@[expose] def IsXiPlus (T X : Subgroup G) : Prop := IsXi T X ∧ ¬ IsXiMinus T X

end CFSG.Quasithin
