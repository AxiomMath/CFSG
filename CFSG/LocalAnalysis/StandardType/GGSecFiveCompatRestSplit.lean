module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Inputs

theorem ggSecFiveCompatRestInput_of_split (hW : GGSecFiveCompatRestWInput)
    (hN : GGSecFiveCompatRestNInput) : GGSecFiveCompatRestInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hd t n f ψ hpres hL
  by_cases hw : GGSecFiveWeylCase p B Bs x D J
  · exact hW G p B Bs x L D J hcfg hOp hInn hNT hw hd t n f ψ hpres hL
  · exact hN G p B Bs x L D J hcfg hOp hInn hNT hw hd t n f ψ hpres hL

end Inputs

end CFSG.StandardType

end
