module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Subgroup

theorem k67_p_ne_three {J : Type} [Group J] [Finite J] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel J .PSL 2 p f)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 1) : p ≠ 3 := by
  intro hp3
  subst hp3
  obtain ⟨hp, hf, -, h3, -⟩ := CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := J)
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup J) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by
      simpa [Subgroup.relIndex_top_right] using P.not_dvd_index⟩
  obtain ⟨hel, hcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22q_psl2_sylow_elem hp (by norm_num) h hS
  have hle : f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hel hcard
  have hf1 : f = 1 := by omega
  exact h3 (by rw [hf1]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
