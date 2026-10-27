module

public import CFSG.LocalAnalysis.StandardType.GGK1ScExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggK0Schur_exc
    : GGK0Schur GGKacGeneric := by
  intro p lab hlab hgen
  refine (largeEvenLabelAll_centerPrime_exc hlab hgen).mono fun R _ I F hR => ?_
  intro L' _ _ ψ hψ hker hperf
  exact ((Nat.Prime.coprime_iff_not_dvd hgen.1).mpr (hR L' ψ hψ hker hperf)).symm

end CFSG.StandardType

end
