module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2C
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NN

import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DProof
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem not_normal_of_ncard_conjSetOf_eq_two {M L : Subgroup G} (hL : L ∈ calC M)
    (h2 : (conjSetOf M L).ncard = 2) : ¬ (L.subgroupOf M).Normal := by
  intro hN
  obtain ⟨K, hKne, hset, -⟩ := uc22s21ru4e_exists_second_member h2 hL
  have hK : K ∈ conjSetOf M L := by
    rw [hset]
    exact Or.inr rfl
  obtain ⟨g, hg, rfl⟩ := hK
  have hgN : g ∈ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (PartTwo.s13_le_of_mem_calC hL)).mp hN hg
  exact hKne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)

theorem normalizer_le_of_r847E3ThinNN {D : Data G} (h847 : R847E3ThinNN D) :
    ∀ (L : Subgroup G) (n r p : ℕ), L ∈ calC D.M → (conjSetOf D.M L).ncard = 2 →
      (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) → r.Prime → r ≠ 2 → p ∈ D.sig →
        ∀ A : Subgroup G, A ≤ L → Nat.card A = r → normalizer (A : Set G) ≤ D.M := by
  intro L n r p hL h2 hLS hr hr2 hp A hAL hAr
  have hthin : F08.Thin8 L := by
    rcases hLS with h | h
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.thin8_of_isL2 h
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.thin8_of_isSz h
  exact h847 L hL (not_normal_of_ncard_conjSetOf_eq_two hL h2) hthin A hAL r hr hr2 hAr p hp

theorem r8100U2D_of_r847E3ThinNN {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h847 : R847E3ThinNN D) :
    R8100U2D D :=
  r8100U2D_of_r8100U2 (r8100U2_of_normalizer_le hSg h13 (normalizer_le_of_r847E3ThinNN h847))

end CFSG.LocalAnalysis.UniquenessCase.UC22
