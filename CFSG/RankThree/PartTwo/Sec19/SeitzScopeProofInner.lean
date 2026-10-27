module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.UnitaryToralNine
public import CFSG.LieType.SeitzGeneration.ClassicalAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 TauCeti

theorem three_le_card_of_valid_twistedA_two {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) : 3 ≤ q.card :=
  ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).2 rfl

theorem seitzThreeLThreePiInner :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsLThreePiIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, rfl, q, hd | hd⟩
  · subst hd
    by_cases hlift : CentralPrimeFree 3 (.A 2 q)
    · exact seitzInnerLinearThreeAb ⟨.A 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hinner, rfl, ⟨2, q, rfl⟩, hlift⟩
    · exact seitzInnerLinearThree ⟨.A 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hinner, rfl, ⟨2, q, rfl⟩, hlift⟩
  · subst hd
    have hq3 := three_le_card_of_valid_twistedA_two hv
    by_cases hlift : CentralPrimeFree 3 (.twistedA 2 q)
    · refine seitzInnerUnitaryThree ⟨.twistedA 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hinner, rfl, ⟨2, q, rfl⟩, hlift, fun m' q' h => ?_⟩
      cases h
      omega
    · have hl : 3 ∣ q.card + 1 ∧ 3 ∣ 2 + 1 := by simpa [CentralPrimeFree] using hlift
      exact seitzInnerUnitaryNonab unitaryHeisCore unitaryToralNine ⟨.twistedA 2 q, hv⟩ 3 hp hp2
        hpd hex E hE hc ⟨hinner, rfl, q, rfl, hl.1⟩

theorem seitzThreeSec441Inner :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
      ∃ q : PrimePower, d.1 = .A 3 q ∨ d.1 = .twistedA 3 q ∨ d.1 = .B 2 q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, rfl, q, hd | hd | hd⟩
  · subst hd
    exact seitzInnerLinearThreeAb ⟨.A 3 q, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hinner, rfl, ⟨3, q, rfl⟩, by simp [CentralPrimeFree]⟩
  · subst hd
    refine seitzInnerUnitaryThree ⟨.twistedA 3 q, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hinner, rfl, ⟨3, q, rfl⟩, by simp [CentralPrimeFree], fun m' q' h hq2 => ?_⟩
    cases h
    exact hex (isD2SeitzException_unitary_four hq2)
  · subst hd
    exact seitzInnerSymplecticTwo ⟨.B 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hinner, q, rfl⟩

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof
