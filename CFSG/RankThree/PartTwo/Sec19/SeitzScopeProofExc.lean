module

public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicTriality
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2NativePlus
public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2NativeSplit
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2NativeCyclic
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

@[expose] def SeitzThreeSec441Noninner : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsSeitz441Index d.1

@[expose] def SeitzThreeTrialityWide : Prop :=
  SeitzPlanes fun d p E => p = 3 ∧ IsTrialityIndex d.1 ∧
    ((¬ InnerPlane d p E ∧ ¬ NarrowScope p E) ∨ (InnerPlane d p E ∧ ¬ RankLE2 p (Cat d)))

namespace SeitzScopeProof

open CFSG.HardMathSupport.Seitz.G2Anisotropic

section CertsParabolic

theorem seitzThreeReeF4Inner_of (h : SeitzExcAnisotropicReeF4Three) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsReeF4Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, rfl, m, hd⟩
  subst hd
  by_cases hN : NormalizesRSubgroup ⟨.reeF4 m, hv⟩ E
  · exact seitzExcParabolic ⟨.reeF4 m, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hin, IsReeTypeIndex.not_classical (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))), hN⟩
  · exact h ⟨.reeF4 m, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hin, ⟨m, rfl⟩, rfl, CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv, hN⟩

theorem seitzThreeTriality_of_residuals (hA : SeitzExcAnisotropicTrialityThree)
    (hO : SeitzExcOuterNarrowTrialityThree) (hW : SeitzThreeTrialityWide) :
    SeitzThreeTriality := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, hd⟩
  by_cases hin : InnerPlane d p E
  · by_cases hN : NormalizesRSubgroup d E
    · exact seitzExcParabolic d p hp hp2 hpd hex E hE hc ⟨hin, IsTrialityIndex.not_classical hd, hN⟩
    · by_cases hr : RankLE2 p (Cat d)
      · exact hA d p hp hp2 hpd hex E hE hc ⟨hin, hd, hp3, hr, hN⟩
      · exact hW d p hp hp2 hpd hex E hE hc ⟨hp3, hd, Or.inr ⟨hin, hr⟩⟩
  · by_cases hs : NarrowScope p E
    · exact hO d p hp hp2 hpd hex E hE hc ⟨hin, hs, hd, hp3⟩
    · exact hW d p hp hp2 hpd hex E hE hc ⟨hp3, hd, Or.inl ⟨hin, hs⟩⟩

end CertsParabolic

section Certs

theorem seitzThreeG2Inner :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsG2Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, rfl, q, hd⟩
  subst hd
  have hq3 : 3 ≠ q.p := by
    have h := hpd
    rwa [show (⟨TauCeti.LieTypeIndex.G2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic =
      q.p from TauCeti.LieTypeIndex.characteristic_G2 q] at h
  by_cases hN : NormalizesRSubgroup ⟨.G2 q, hv⟩ E
  · exact seitzExcParabolic ⟨.G2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hin, IsG2Index.not_classical ⟨q, rfl⟩, hN⟩
  · exact Coordinator.seitzExcAnisotropicG2_of_parts
      CFSG.HardMathSupport.Seitz.ExceptionsTransport.g2NativePlaneGenSplit_proved
      UnitaryEmbedding.g2NativePlaneGenPlus_proved Coordinator.g2NativePlaneGenCyclic ⟨.G2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hin, ⟨q, rfl⟩, Coordinator.rankLE2_three_cat_G2 q hv hq3, hN⟩

end Certs

end SeitzScopeProof

end CFSG.RankThree.PartTwo.Sec19
