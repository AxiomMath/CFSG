module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_15C (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → ∀ n : ℕ,
    (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) → ∀ p ∈ D.sig,
      (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])

@[expose] def S21_9N (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal → ∀ n : ℕ,
    IsSU3 (Bar2 L) n → ¬ IsPowTwo n → CFSG.Open.evenRank G = 3

namespace P2214S

theorem sz_cong_of_s21_15C {D : Data G} {Ch : Choice2011 G} (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n) {p : ℕ}
    (hp : p ∈ D.sig) : (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)] := by
  rcases h15 h1930 c L hL hc2 n (Or.inl hSz) p hp with ⟨hL2, -⟩ | ⟨-, h⟩
  · exact (uc22p22g_isSz_isL2_false hSz hL2).elim
  · exact h

end P2214S

end CFSG.LocalAnalysis.UniquenessCase.UC22
