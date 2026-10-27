module

public import CFSG.Sporadic.Co1.Module.InvClass
public import CFSG.Monster.B.TwoA.Census.LatticeInv
public import CFSG.Sporadic.Co1.Module.InvAssemble

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.TwoA.Census

theorem co1InvolutionFacts :
    Co1InvolutionFacts := by
  obtain ⟨-, -, hmem, hcls, -⟩ := lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := CFSG.Sporadic.Co1.Module.exists_conj_three_of_chevalley monoN hmem hcls
  exact co1InvolutionFacts_of_classes c hc

end CFSG.Monster.GMS
