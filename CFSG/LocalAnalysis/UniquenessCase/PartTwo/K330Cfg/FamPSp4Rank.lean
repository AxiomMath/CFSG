module

import CFSG.Adapters.LieModelL4U4Sp4Torus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem rank_PSp4 {J : Type} [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSp 2 p f)
    (hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1) : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup J) := by
  have hp : p.Prime := e.admissible.1
  have hf : 1 ≤ f := e.admissible.2.1
  rcases hcase with hp7 | h7
  · subst hp7
    have hcl : StatedClassicalModel J .PSp 2 7 f :=
      e.statedClassicalModel_of_ne_zero (by norm_num)
    obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (p := 7) (n := 2) (f := f)
      (by norm_num) hcl
    rcases hr with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, hPSp⟩ | h4
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · rcases hPSp with ⟨-, hle⟩ | hle <;> omega
    · omega
  · have hfac : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      simpa using Nat.sq_sub_sq (p ^ f) 1
    rw [hfac] at h7
    rcases Nat.prime_seven.dvd_mul.mp h7 with hplus | hminus
    · exact LieModel.two_le_pRank_psp4_of_dvd e Nat.prime_seven (by norm_num) (Or.inr hplus)
    · exact LieModel.two_le_pRank_psp4_of_dvd e Nat.prime_seven (by norm_num) (Or.inl hminus)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
