module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactL2Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactL2Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactL3Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactU3Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactOdd
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kFactShape92L28_holds :
    ∀ (Q : Type) [Group Q] [Finite Q], F09.Shape92 Q →
      (∀ P : Subgroup Q, IsPGroup 3 ↥P → IsCyclic ↥P) →
      ∀ X W T : Subgroup Q, KCfgL28 X W T → W = ⊤ := by
  intro Q _ _ hQ hcyc X W T c
  rcases hQ with ⟨-, h3⟩ | hJ | ⟨p, f, hL2⟩ | ⟨p, f, hpf, hL3⟩ | ⟨p, f, hpf, hU3⟩
  · exact (kFactL28_not_three_group h3 c).elim
  · exact (kFactL28_not_J1 hJ c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL28_L2_even hL2 hcyc c
    · exact (kFactL28_L2_odd hp hL2 c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL28_L3_even hpf hL3 c
    · exact (kFactL28_L3U3_odd hp (Or.inl hL3) c).elim
  · by_cases hp : p = 2
    · subst hp
      exact kFactL28_U3_even hU3 c
    · exact (kFactL28_L3U3_odd hp (Or.inr hU3) c).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
