module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B8Main
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_17RPow (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
    (∀ n : ℕ, IsPowTwo n → ¬ IsSU3 (Bar2 L) n) ∧
    (∀ n : ℕ, IsPowTwo n → IsL2 (Bar2 L) n → (conjSetOf D.M L).ncard ≤ 2) ∧
    ((conjSetOf D.M L).ncard = 2 → IsL2 (Bar2 L) 2 → IsPowTwo c.n) ∧
    (∀ q : ℕ, q.Prime → 5 < q → ¬ IsL2Odd (Bar2 L) q) ∧
    (IsJ1 (Bar2 L) → CFSG.Open.evenRank G = 3)

theorem s21_17R_of_s21_17RPow
    {D : Data G} {Ch : Choice2011 G}
    (hG : CFSG.Open.GriessAllModelsStatement) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h : S21_17RPow D Ch) :
    S21_17R D Ch := fun hH c L hL hnN => by
  obtain ⟨h1, h2⟩ := h hH c L hL hnN
  refine ⟨fun n => ?_, h2⟩
  by_cases hn : IsPowTwo n
  · exact h1 n hn
  · exact uc22s217u3b_not_isSU3_of_griess hG D Ch h211 hH c hSg h76 hL hnN hn

end CFSG.LocalAnalysis.UniquenessCase.UC22
