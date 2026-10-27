module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22pwGood (D : Data G) (L : Subgroup G) (n : ℕ) (E : Subgroup (Bar2 L)) : Prop :=
  E ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ∧ IsMulCommutative E ∧
    Odd (Nat.card E) ∧
    (∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2) ∧
    piSet E = etaSet n ∧
    (∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T → ∀ x ∈ E,
      uc22p20uInd L t ht x ∈ E ⊔ uc22p20iSylowBar D L) ∧
    (∀ e m : ℕ, Odd m → n = 2 ^ e * m → ∀ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T →
      ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m - 1} E, uc22p20uInd L t ht x * x⁻¹ ∈ uc22p20iSylowBar D L) ∧
    ∃ w : Bar2 L, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ⊔
        Subgroup.zpowers w = ⊤

end CFSG.LocalAnalysis.UniquenessCase.UC22
