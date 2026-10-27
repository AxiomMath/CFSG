module

public import CFSG.RankThree.PartOne.S12.Sec1511Y4Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace AUTSL

@[expose] def KF1511BTAt (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ),
    Blueprint.LieModel X t n 2 f →
    ∀ S : Subgroup X, S ≠ ⊥ → IsPGroup 2 ↥S →
      Open.pCoreOf 2 (Subgroup.normalizer (S : Set X)) = S →
      Subgroup.normalizer (S : Set X) ≠ ⊤ →
      (∃ S₀ : Sylow 2 X, Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤
        Subgroup.normalizer (S : Set X)) →
      ∀ B : Subgroup X, B ≤ Subgroup.normalizer (S : Set X) → IsElementaryAbelian 5 ↥B →
        Nat.card ↥B = 25 →
      ∀ α : MulAut X, S.map α.toMonoidHom = S → B.map α.toMonoidHom = B →
        (∀ b ∈ B, (α ^ 3) b = b) → (∃ b ∈ B, α b ≠ b) →
      ∀ (Q : Type) [Group Q] [Finite Q] (ρ : Q →* MulAut X), IsPGroup 2 Q →
        (∀ q, S.map (ρ q).toMonoidHom = S) → (∀ q, ∀ b ∈ B, b⁻¹ * ρ q b ∈ S) →
        ∃ Δ : Subgroup X, (∀ d ∈ Δ, ∀ q, d⁻¹ * ρ q d ∈ S) ∧ Sec1511.HasNonabSimpleSection 5 ↥Δ

@[expose] def KF1511BTL4 : Prop := KF1511BTAt .PSL 4

@[expose] def KF1511BTSp6 : Prop := KF1511BTAt .PSp 3

@[expose] def KF1511BTOm8m : Prop := KF1511BTAt .POmegaMinus 4

theorem kf1511BT_of_rows (h4 : KF1511BTL4) (h6 : KF1511BTSp6) (h8 : KF1511BTOm8m) :
    Sec1511.KF1511BT := by
  intro X _ _ t n f hmodel hrow
  rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h4 X f hmodel
  · exact h6 X f hmodel
  · exact h8 X f hmodel

theorem kf1511BT_iff_rows :
    Sec1511.KF1511BT ↔ KF1511BTL4 ∧ KF1511BTSp6 ∧ KF1511BTOm8m :=
  ⟨fun h => ⟨fun X _ _ f hmodel => h X .PSL 4 f hmodel (Or.inl ⟨rfl, rfl⟩),
      fun X _ _ f hmodel => h X .PSp 3 f hmodel (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      fun X _ _ f hmodel => h X .POmegaMinus 4 f hmodel (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩,
    fun ⟨h4, h6, h8⟩ => kf1511BT_of_rows h4 h6 h8⟩

end AUTSL

end CFSG.RankThree.PartOne
