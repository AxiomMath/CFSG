module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s21_17R_one_pow_of_three (he : evenRank G = 3) (hG : GriessAllModelsStatement)
    (D : Data G) (Ch : Choice2011 G) :
    H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
      ∀ n : ℕ, IsPowTwo n → ¬ IsSU3 (Bar2 L) n := by
  intro _ _ L hL hnN n hn hX
  have hn2 : 2 ≤ n := UCK.u3Range (Bar2 L) n hX
  have hn3 : n ≠ 3 := by
    rintro rfl
    exact s13_not_isPowTwo_of_prime Nat.prime_three (by norm_num) hn
  obtain ⟨q, hq, hq3, hqn⟩ := UC6S898.exists_prime_gt_three_dvd hn2 hn3
  have hq2 : q ≠ 2 := by omega
  have hZq : ¬ q ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (UCK.u3Center_of_griess hG _ n hX))
    omega
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  obtain ⟨E, hEL, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_sq_of_isSU3 (UCK.u3Syl_of_griess hG) hX hq hq3 hqn
  have h4 : 2 * 2 ≤ Open.pRank q D.M :=
    UC6S846.calCRankTwice D.M L hL hnN' q hq hq2 hZq E hEL hEel 2 hEc
  have h3 : Open.pRank q D.M ≤ evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 D.M D.maxLocal.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
