module

public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_centerPrime_clC
    {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGenericClC lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hgen, htag⟩ := hgen
  dsimp only at hgen htag hlab ⊢
  have hn1 : 1 ≤ n := hlab.1
  have hp : p.Prime := hgen.1
  have hp2 : p ≠ 2 := hgen.2.1
  intro Q hQ
  rcases htag with hB | hC
  · subst hB
    have hr2 : 2 ≤ r := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
    refine ⟨K, i1, i2, hK, hQR, ?_⟩
    letI := i1
    letI := i2
    haveI : CharP K 2 := charP_two_of_card hK
    haveI : NeZero r := ⟨by omega⟩
    exact ggCenterPrime_sp hp hp2
  · subst hC
    have hr2 : 2 ≤ r := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
    refine ⟨K, i1, i2, hK, hQR, ?_⟩
    letI := i1
    letI := i2
    haveI : CharP K 2 := charP_two_of_card hK
    haveI : NeZero r := ⟨by omega⟩
    exact ggCenterPrime_sp hp hp2

end CFSG.StandardType

end
