module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R8100U2 (D : Data G) : Prop :=
  evenRank G = 3 → ∀ (L : Subgroup G) (n s r p : ℕ), L ∈ calC D.M →
    (conjSetOf D.M L).ncard = 2 →
    ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) →
    Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → p ∈ D.sig →
    ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22
