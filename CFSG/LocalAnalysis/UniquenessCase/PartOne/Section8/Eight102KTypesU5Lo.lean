module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU5Res
import CFSG.LocalAnalysis.WeakClosure81.W183FUBorel
import CFSG.RankThree.PartOne.KF.LayerModelRow
import CFSG.RankThree.PartTwo.KFacts.KS222U5
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (bA6)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem two_le_pRank_five_centralizer_bA6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    2 ≤ Open.pRank 5 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) := by
  let Z : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)) :=
    (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      centralizer (zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))
  let D : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)) := F08.DerInf8 Z
  change 2 ≤ Open.pRank 5 Z
  have hnon : Nonempty (D ≃* SU (unitaryInvolution K 2 2) 3) :=
    nonempty_derInf8_bA6 hK hζ h1 h3
  have hlie : IsU3 ↥(SU (unitaryInvolution K 2 2) 3) 2 :=
    CFSG.RankThree.PartOne.lieModel_of_scm_psu
      (CFSG.RankThree.PartTwo.Sec21.U5Lines.statedClassicalModel_SU_three hK)
  obtain ⟨e⟩ := hnon
  have hlieD : IsU3 ↥D 2 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hlie
  have hrank : 2 ≤ Open.pRank 5 (⊤ : Subgroup ↥D) :=
    CFSG.LocalAnalysis.WeakClosure81.w183fu_two_le_pRank_five hlieD
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5) D] at hrank
  refine hrank.trans (CFSG.SectionRank.pRank_mono (p := 5) (by norm_num) ?_)
  exact Subgroup.map_subtype_le _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
