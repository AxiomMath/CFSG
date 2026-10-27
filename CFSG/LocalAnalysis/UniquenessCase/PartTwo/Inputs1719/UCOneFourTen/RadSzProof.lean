module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadicalSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzLayer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.RadSzRee
import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem radicalSzComponent_holds :
    RadicalSzComponent := by
  intro S _ _ U n hS hev hU _ hrad hcomp
  obtain ⟨B, hB, hBsz⟩ := hcomp
  obtain ⟨t, m, f, hadm, hm⟩ := hev
  obtain ⟨hBs, -, -, -, hB2, hB3, -⟩ := isSz_facts hBsz
  have hPtop := normalizer_ne_top_of_isComponentOf hS hU hrad hB
  by_cases hTits : t = .Tits
  · subst hTits
    obtain ⟨-, -, hm0, -, -⟩ := hadm
    subst hm0
    refine (false_of_lieModel_tits_of_isSz hm hBsz ?_).elim
    exact (Subgroup.card_subgroup_dvd_card B).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _))
  have hBT := CFSG.LieType.BorelTits.holds_of_lieModel hm hTits
  obtain ⟨T, hTU⟩ := exists_sylow_normalizer_le_of_radical hBT hU hrad
  obtain ⟨J₀, hTJ, hJU, hNJ, hJT, hJ3⟩ := exists_threePrime_sylow_overgroup T hTU hB hBs hB2 hB3
  have hPT : normalizer (U : Set S) ≠ normalizer ((T : Subgroup S) : Set S) :=
    fun e => hJT (e ▸ hJU)
  by_cases hSz : t = .twistedB2
  · subst hSz
    exfalso
    rcases hm with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hree, -⟩ | ⟨-, -, hsz⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact absurd hree (by decide)
    · exact false_of_suzukiModel_of_ne hsz T hTU hPtop hPT
  by_cases hF4 : t = .twistedF4
  · subst hF4
    obtain ⟨-, -, hm0, -⟩ := hadm
    subst hm0
    rw [eq_of_lieModel_twistedF4_of_isComponentOf hm hrad T hTU hPtop hPT hB hBsz]
    exact hm
  exact absurd (three_dvd_card_of_hasBorelModel (hasBorelModel_of_lieModel hm hSz hF4 hTits) T hTJ
    hNJ hJT) hJ3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
