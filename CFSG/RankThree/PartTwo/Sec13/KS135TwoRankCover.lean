module

public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleTwoRank
public import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCoverSporadic
import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCoverLinear
import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCoverUnitary
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree.PartTwo

theorem ks135TwoRankCover :
    KS135TwoRankCover := by
  intro J _ _ hq hZ2 hZ1 htype
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  rcases htype with hM | hJ | ⟨f, hf, hL⟩
  · obtain ⟨e⟩ := hM
    exact KS135Cover.three_le_pRank_of_m12_cover hq hZ2 hZ1 e
  · obtain ⟨e⟩ := hJ
    exact KS135Cover.three_le_pRank_of_j2_cover hq hZ2 hZ1 e
  · rcases hL with ⟨h3, ⟨e⟩⟩ | ⟨h3, ⟨e⟩⟩
    ·
      have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        norm_num at h3
      have hK : 4 ≤ Nat.card (GaloisField 2 f) := by
        rw [GaloisField.card 2 f (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact KS135Cover.three_le_pRank_of_projSL_cover hK
        (φ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)))
        (e.surjective.comp (QuotientGroup.mk'_surjective _)) (KS135Cover.ker_comp_mk' e) hZ2
        hZ1
    ·
      by_cases hf1 : f = 1
      · subst hf1
        exfalso
        have hs := isSolvable_projSU_two
        have hZs : Group.IsSolvable (Subgroup.center J) :=
          Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
        have hsJ : Group.IsSolvable J :=
          Group.isSolvable_of_ker_le_range (Subgroup.center J).subtype
            (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)))
            (by rw [KS135Cover.ker_comp_mk' e, Subgroup.range_subtype])
        have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hq
        have : Group.IsPerfect J := hq.1
        exact Group.IsPerfect.not_isSolvable J hsJ
      · have hf3 : 3 ≤ f := by
          by_contra hlt
          obtain rfl : f = 2 := by omega
          norm_num at h3
        exact KS135Cover.three_le_pRank_of_projSU_cover hf3 h3
          (φ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)))
          (e.surjective.comp (QuotientGroup.mk'_surjective _)) (KS135Cover.ker_comp_mk' e).le

end CFSG.RankThree.PartTwo.Sec13
