module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem kgFieldRestrictionOn_linear : KGFieldRestrictionOn (kgfniRow .linear) := by
  intro p lab hp hp2 hΛ _ht3 hrow
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, _hpn⟩ := hrow
  have htA : t = .A := htag
  subst htA
  obtain ⟨hn, hl, -⟩ := hΛ
  have hl' : 1 ≤ l := hl
  have hn' : 1 ≤ n := hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  intro f hf hfo h hh hhp hcomm J₀ hJ₀ f' hf'
  exact kgFieldRestriction_of_oneMarking f'
    (fniLin_oneMarking (N := l + 1) (n := n) (p := p) (by omega) hn hp hp2 hK hf hfo hh hhp hcomm
      ((CFSG.Assembly.isComponentOf_iff_open).1 hJ₀) f' hf')

end CFSG.StandardType
