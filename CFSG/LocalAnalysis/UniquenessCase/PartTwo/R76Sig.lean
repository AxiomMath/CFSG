module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R76Sig (D : Data G) : Prop :=
  ∀ p ∈ D.sig, p ≠ 2 → IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian r E → Nat.card E = r ^ 2 →
      0 < Open.pRank p (D.M ⊓ centralizer (E : Set G)) →
      (∀ X : Subgroup G, X ≤ E → Nat.card X = r →
        1 < Open.pRank p (D.M ⊓ normalizer (X : Set G))) →
        rankThreeGamma 1 r E ≤ D.M

theorem R76Sig_of_R76 (D : Data G) (h : R76 D) : R76Sig D := fun p hp hp2 hsp =>
  h p (D.sig_prime p hp).1 hp2 hsp

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
