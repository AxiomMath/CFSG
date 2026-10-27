module

public import CFSG.LocalAnalysis.StandardType.GGK1ScLaneA
public import CFSG.LocalAnalysis.StandardType.GGK1ScLaneC
public import CFSG.LocalAnalysis.StandardType.GGK1ScLaneD

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_centerPrime_cl
    {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGenericCl lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  rcases ggKacGenericCl_lanes hlab hgen with h | h | h
  · exact largeEvenLabelAll_centerPrime_clA hlab h
  · exact largeEvenLabelAll_centerPrime_clC hlab h
  · exact largeEvenLabelAll_centerPrime_clD hlab h

theorem ggK0Schur_cl :
    GGK0Schur GGKacGenericCl := by
  intro p lab hlab hgen
  refine (largeEvenLabelAll_centerPrime_cl hlab hgen).mono fun R _ I F hR => ?_
  intro L' _ _ ψ hψ hker hperf
  exact ((Nat.Prime.coprime_iff_not_dvd hgen.1).mpr (hR L' ψ hψ hker hperf)).symm

end CFSG.StandardType

end
