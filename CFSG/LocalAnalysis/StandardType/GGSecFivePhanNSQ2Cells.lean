module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSQ2Input_of_cells
    (hL : GGSecFiveNSQ2LInput) (hN : GGSecFiveNSQ2NbrInput) : GGSecFiveNSQ2Input := by
  intro hTBF hWA hLB hP G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hA hno6 X hX hXns hlab
  rcases hX with hXL | hXn
  · rw [hXL] at hlab
    have h35 : GGInnerDiagOnLabel
        (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5)) p Bs L :=
      hlab.mono' fun lab hl => by
        obtain ⟨h1, h2, h3 | h3⟩ := hl
        exacts [Or.inl ⟨h1, h2, h3⟩, Or.inr ⟨h1, h2, h3⟩]
    rcases GGInnerDiagOnLabel.elim_or h35 with h3 | h5
    · refine not_ggInnerDiagOnLabel_unitary_four hcfg.1.1 (h3.mono' fun lab hl => ?_)
      obtain ⟨⟨hlab', hdvd⟩, -, hr⟩ := hl
      refine ⟨?_, hr, hdvd⟩
      rcases hlab' with ⟨ht, -⟩ | ⟨ht, -⟩
      exacts [Or.inl ht, Or.inr ht]
    · exact hL hTBF hWA hLB hP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hA hno6 h5
  · exact hN hTBF hWA hLB hP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hA hno6 X hXn hXns hlab

end CFSG.StandardType

end
