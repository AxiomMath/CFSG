module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.Q1327.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

@[expose] def Sp6Cell (p : ℕ) (X : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 f

@[expose] def Om8Cell (p : ℕ) (X : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 2 f

@[expose] def KF1327Refl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X A₀ F : Subgroup G), Q1327.T123Base p X A₀ F →
    (RowModel p X 10 ∨ Sp6Cell p X ∨ Om8Cell p X) →
    ∀ t ∈ torusImage F X, IsAutReflection p F t → ∀ c₀ ∈ autMovedInG F t, c₀ ≠ 1 →
      ∃ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G), ¬ Commute c₀ (y * c₀ * y⁻¹)

theorem KF1327Refl.false_of_commute (hR : KF1327Refl) [Finite G] {p : ℕ} {X A₀ F : Subgroup G}
    (h : Q1327.T123Base p X A₀ F) (ho : RowModel p X 10 ∨ Sp6Cell p X ∨ Om8Cell p X)
    {t : MulAut ↥F} (ht : t ∈ torusImage F X) (hrefl : IsAutReflection p F t) {c₀ : G}
    (hc₀ : c₀ ∈ autMovedInG F t) (hc₀1 : c₀ ≠ 1)
    (hcomm : ∀ y₁ ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G),
      ∀ y₂ ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G),
        Commute (y₁ * c₀ * y₁⁻¹) (y₂ * c₀ * y₂⁻¹)) : False := by
  obtain ⟨y, hy, hnc⟩ := hR G p X A₀ F h ho t ht hrefl c₀ hc₀ hc₀1
  have h1 := hcomm 1 (Subgroup.one_mem _) y hy
  rw [one_mul, inv_one, mul_one] at h1
  exact hnc h1

end CFSG.RankThree.PartOne.Q1327Z
