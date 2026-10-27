module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex
import CFSG.LocalAnalysis.UniquenessCase.UC22K331L3EvenA8
import CFSG.LocalAnalysis.UniquenessCase.UC22K331L3EvenMat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Open (StatedClassicalModel)
open CFSG.Quasithin.H13.CTK (TwoGroupsClassTwo)
open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls (statedClassical_of_lieModel)

theorem k331Idx_l3Even_A {q : PrimePower} (hv : (LieTypeIndex.A 2 q).Valid) (hq2 : q.p = 2) :
    K331Idx (.lie ⟨.A 2 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩ T _ K hK _
  exfalso
  have e' : L ≃* Cat ⟨.A 2 q, hv⟩ := e
  have hmodel : StatedClassicalModel L .PSL (2 + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A 2 q hv e')
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two q.exponent_pos (by rw [hF, hq2])
  exact not_isAlt_bar2_of_twoGroupsClassTwo
    (TwoGroupsClassTwo.of_mulEquiv eF (twoGroupsClassTwo_statedProj le_rfl)) K hK

theorem k331Idx_l3Even_twistedA {q : PrimePower} (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (hq2 : q.p = 2) : K331Idx (.lie ⟨.twistedA 2 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩ T _ K hK _
  exfalso
  have e' : L ≃* Cat ⟨.twistedA 2 q, hv⟩ := e
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : StatedClassicalModel L .PSU (2 + 1) q.p q.exponent := by
    have := statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedA 2 q hv e')
    rwa [hc, hf] at this
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := q.exponent * 2) (by have := q.exponent_pos; omega)
    (by rw [hF, hq2, ← pow_mul])
  exact not_isAlt_bar2_of_twoGroupsClassTwo (TwoGroupsClassTwo.of_mulEquiv eF
    (twoGroupsClassTwo_statedProj (CFSG.Open.StatedAPI.statedSU_le_statedSL _ _ F))) K hK

theorem k331_l3Even : K331Fam K331L3Even := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | A r q =>
      obtain ⟨rfl, hq⟩ := hi
      exact k331Idx_l3Even_A hv hq
    | twistedA r q =>
      obtain ⟨rfl, hq⟩ := hi
      exact k331Idx_l3Even_twistedA hv hq
    | _ => exact False.elim hi
  · exact False.elim hi

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
