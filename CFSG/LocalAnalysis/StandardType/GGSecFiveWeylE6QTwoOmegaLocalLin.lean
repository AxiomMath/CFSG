module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux2

public section

namespace CFSG.StandardType.E6QTwo

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def omPlusLin (hK : Nat.card K = 2) {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (l : ↥L) :
    (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  ((CFSG.StandardType.OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap θ l) :
    ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4))) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))

end CFSG.StandardType.E6QTwo

end
