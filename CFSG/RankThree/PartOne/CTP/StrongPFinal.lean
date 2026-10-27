module

public import CFSG.RankThree.PartOne.CTP.StrongPBridge
public import CFSG.RankThree.PartOne.CTP.AltLeaf

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne ExtSeitz ExtSPE)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.RankThree.PartOne.StrongP
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem extSPE_of_inputs (hThree : ThreeCatalog) (hSeitz : ExtSeitz) (hBridge : SeitzBridge)
    (hSchr : SchreierFor CFSG.Assembly.InCatalog) (hCharP : CharPNoncommInput)
    (hSpor : SporadicStrongPInput) : ExtSPE := by
  intro p hp hp5 H _ _ S hSn hhyp hSc Y hY P hP hab hcard
  have : Fact p.Prime := ⟨hp⟩
  have := hSn
  have hlist : TheoremThreeList ↥S := hThree ↥S hhyp
  show SPEConclusion p ↥S
  obtain ⟨Y', E, hY', hEY, hEab, hEc⟩ := exists_pair_le hY hP hab hcard
  have := hEab
  have seitz : ∀ {d : TauCeti.LieTypeIndex}, IsoLie ↥S d → d.characteristic ≠ p →
      SPEConclusion p ↥S := fun hiso hne =>
    spe_conclusion_of_seitz hSeitz hBridge hSchr hp5 S hhyp hSc hY' hEY hEc hiso hne
  have seitz2 : ∀ {d : TauCeti.LieTypeIndex}, IsoLie ↥S d → d.characteristic = 2 →
      SPEConclusion p ↥S := fun hiso hd => seitz hiso (by rw [hd]; omega)
  have noncomm : HasNoncommPair p ↥S → SPEConclusion p ↥S := fun h =>
    (false_of_hasNoncommPair S hP hab h).elim
  have hL := hlist
  rcases hlist with ⟨q, hq2, h5, hiso⟩ | ⟨q, hq2, hexp, hiso | hiso⟩ | hiso |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso⟩ | ⟨n, hn5, hn12, ⟨e⟩⟩ | h6 |
    (⟨q, hq2, hiso⟩ | ⟨m, hiso⟩ | ⟨q, hq2, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩ |
      ⟨m, hiso⟩ | hiso) | ⟨q, hq2, hiso | hiso | hiso⟩ |
    ⟨q, hq2, hq1, hiso | hiso | hiso | hiso | hiso | hiso | hiso⟩
  ·
    by_cases hqp : q.p = p
    · exact spe_conclusion_A1 hp5 S hSc hP hcard hqp hiso
    · exact seitz hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hasNoncommPair_of_isoLie_A hp5 (le_refl 2) hqp hiso)
    · exact seitz hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inl hiso))
    · exact seitz hiso (by simpa using hqp)
  ·
    exact seitz hiso (by simp; omega)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inr (Or.inr hiso))))
    · exact seitz hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inr (Or.inl hiso))))
    · exact seitz hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hCharP p hp hp5 ↥S q hqp (Or.inr (Or.inl hiso)))
    · exact seitz hiso (by simpa using hqp)
  ·
    by_cases hqp : q.p = p
    · exact noncomm (hasNoncommPair_of_isoLie_A hp5 (by norm_num) hqp hiso)
    · exact seitz hiso (by simpa using hqp)
  ·
    obtain ⟨hp5', hn10⟩ := alt_stronglyPEmbedded hp5 hn5 hn12 S e hSc hY' hEY hEc
    subst hn10
    exact Or.inr ⟨hp5', Or.inl ⟨e⟩⟩
  ·
    exact (hSpor p hp hp5 H S hSn hhyp.isSimpleGroup hhyp.nonabelian h6 hSc Y hY P hP hab
      hcard).elim
  ·
    exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simp)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simp)
  · exact seitz2 hiso (by simp)
  ·
    exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  ·
    exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)
  · exact seitz2 hiso (by simpa using hq2)

theorem extSPE_of_rest (hThree : ThreeCatalog) (hSeitz : ExtSeitz) (hRest : SeitzBridgeRest)
    (hSchr : SchreierFor CFSG.Assembly.InCatalog) (hCharP : CharPNoncommInput)
    (hSpor : SporadicStrongPInput) : ExtSPE :=
  extSPE_of_inputs hThree hSeitz (seitzBridge_of_rest hRest) hSchr hCharP hSpor

end CFSG.RankThree.PartOne.CTP
