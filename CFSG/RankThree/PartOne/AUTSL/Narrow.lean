module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace AUTSL

@[expose] def KF1511BTEAt (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ),
    Blueprint.LieModel X t n 2 f →
    ∀ S : Subgroup X, S ≠ ⊥ → IsPGroup 2 ↥S →
      Open.pCoreOf 2 (Subgroup.normalizer (S : Set X)) = S →
      Subgroup.normalizer (S : Set X) ≠ ⊤ →
      (∃ S₀ : Sylow 2 X, Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤
        Subgroup.normalizer (S : Set X)) →
      ∀ E : Subgroup X, IsElementaryAbelian 5 ↥E → Nat.card ↥E = 125 →
      ∀ B : Subgroup X, B ≤ E → B ≤ Subgroup.normalizer (S : Set X) → Nat.card ↥B = 25 →
      ∀ α : MulAut X, S.map α.toMonoidHom = S → B.map α.toMonoidHom = B →
        (∀ b ∈ B, (α ^ 3) b = b) → (∃ b ∈ B, α b ≠ b) →
      ∀ (Q : Type) [Group Q] [Finite Q] (ρ : Q →* MulAut X), IsPGroup 2 Q →
        (∀ q, S.map (ρ q).toMonoidHom = S) → (∀ q, ∀ b ∈ B, b⁻¹ * ρ q b ∈ S) →
        E ≤ Subgroup.normalizer (S : Set X) ∧ ∀ q, ∀ e ∈ E, e⁻¹ * ρ q e ∈ S

@[expose] def KF1511BTEL4 : Prop := KF1511BTEAt .PSL 4

@[expose] def KF1511BTESp6 : Prop := KF1511BTEAt .PSp 3

@[expose] def KF1511BTEOm8m : Prop := KF1511BTEAt .POmegaMinus 4

@[expose] def KF1511BTE : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
    Blueprint.LieModel X t n 2 f →
    ((t = .PSL ∧ n = 4) ∨ (t = .PSp ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) →
    ∀ S : Subgroup X, S ≠ ⊥ → IsPGroup 2 ↥S →
      Open.pCoreOf 2 (Subgroup.normalizer (S : Set X)) = S →
      Subgroup.normalizer (S : Set X) ≠ ⊤ →
      (∃ S₀ : Sylow 2 X, Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤
        Subgroup.normalizer (S : Set X)) →
      ∀ E : Subgroup X, IsElementaryAbelian 5 ↥E → Nat.card ↥E = 125 →
      ∀ B : Subgroup X, B ≤ E → B ≤ Subgroup.normalizer (S : Set X) → Nat.card ↥B = 25 →
      ∀ α : MulAut X, S.map α.toMonoidHom = S → B.map α.toMonoidHom = B →
        (∀ b ∈ B, (α ^ 3) b = b) → (∃ b ∈ B, α b ≠ b) →
      ∀ (Q : Type) [Group Q] [Finite Q] (ρ : Q →* MulAut X), IsPGroup 2 Q →
        (∀ q, S.map (ρ q).toMonoidHom = S) → (∀ q, ∀ b ∈ B, b⁻¹ * ρ q b ∈ S) →
        E ≤ Subgroup.normalizer (S : Set X) ∧ ∀ q, ∀ e ∈ E, e⁻¹ * ρ q e ∈ S

theorem kf1511BTE_of_rows (h4 : KF1511BTEL4) (h6 : KF1511BTESp6) (h8 : KF1511BTEOm8m) :
    KF1511BTE := by
  intro X _ _ t n f hmodel hrow
  rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h4 X f hmodel
  · exact h6 X f hmodel
  · exact h8 X f hmodel

theorem kf1511BTE_iff_rows :
    KF1511BTE ↔ KF1511BTEL4 ∧ KF1511BTESp6 ∧ KF1511BTEOm8m :=
  ⟨fun h => ⟨fun X _ _ f hmodel => h X .PSL 4 f hmodel (Or.inl ⟨rfl, rfl⟩),
      fun X _ _ f hmodel => h X .PSp 3 f hmodel (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      fun X _ _ f hmodel => h X .POmegaMinus 4 f hmodel (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩,
    fun ⟨h4, h6, h8⟩ => kf1511BTE_of_rows h4 h6 h8⟩

end AUTSL

end CFSG.RankThree.PartOne
