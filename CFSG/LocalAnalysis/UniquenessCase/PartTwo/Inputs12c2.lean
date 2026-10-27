module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem148Torus (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G), WeakClosureSetting D V₀ V → V₀ ≠ ⊥ →
    ∀ g : G, InCalOStar (mSub V - 1) D.M V₀ V g → ∃ Y : Subgroup G, IsRegularTorus D.M V g Y

@[expose] def W3Lem148_2 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G) (h : WeakClosureSetting D V₀ V), V₀ ≠ ⊥ →
    ∀ g : G, InCalOStar (mSub V - 1) D.M V₀ V g →
    ∀ Xbar : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)), Xbar ≠ ⊥ →
      Xbar ≤ Mbar D.M V₀ V h.isElemAbelian →
      (∀ m ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar) →
      ⁅Xbar, barSub V₀ V h.isElemAbelian (BOf D.M V g)⁆ = ⊥ →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card Xbar →
        ∃ P : Subgroup G, IsSylowIn p P (preBarSub D.M V₀ V h.isElemAbelian Xbar) ∧
          P ≤ normalizer (NOf D.M V g : Set G)

@[expose] def R1114 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ¬ D.M ⊓ centralizer (V₀ : Set G) ≤ F11.CTilde D.M V₀ V ∧
    ∀ X : Subgroup G, X ≤ D.M → D.M ⊓ centralizer (V : Set G) ≤ X →
      (X : Set G) * (F11.CTilde D.M V₀ V : Set G) = (D.M : Set G) → UniqueMax D.M X

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
