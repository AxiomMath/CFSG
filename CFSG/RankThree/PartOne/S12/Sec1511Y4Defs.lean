module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2Aut

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

@[expose] def KF1511BT : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
    Blueprint.LieModel X t n 2 f →
    ((t = .PSL ∧ n = 4) ∨ (t = .PSp ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) →
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
        ∃ Δ : Subgroup X, (∀ d ∈ Δ, ∀ q, d⁻¹ * ρ q d ∈ S) ∧ HasNonabSimpleSection 5 ↥Δ

end Sec1511

end CFSG.RankThree.PartOne
