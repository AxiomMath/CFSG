module

public import CFSG.Blueprint.Catalog
import CFSG.Adapters.TauCetiExceptional.BridgeG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open TauCeti

theorem chevalleyExceptionalModel_G2_of_odd (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hp2 : q.p ≠ 2) :
    Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
  refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, ?_, ⟨e.symm⟩⟩
  · rw [← PrimePower.card_def]
    exact hq3
  · rw [hK, PrimePower.card_def]

theorem chevalleyExceptionalModel_G2_three (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hp : q.p = 3) (hf : q.exponent = 1) :
    Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 3 1 := by
  have h := chevalleyExceptionalModel_G2_of_odd q hv (by rw [hp]; norm_num)
  rw [hp, hf] at h
  exact h

end CFSG.RankThree.PartTwo.Sec4.Census
