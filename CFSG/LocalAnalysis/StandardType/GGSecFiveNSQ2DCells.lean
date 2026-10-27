module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2DCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
public import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSQ2DInput_of_u6
    (h : GGSecFiveNSQ2DU6Input) : GGSecFiveNSQ2DInput := by
  intro hTBF hWA hLB hP G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hno6 i j hij hMij hno hlab
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
  · exact h hTBF hWA hLB hP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hno6 i j hij hMij hno h5

end CFSG.StandardType

end
