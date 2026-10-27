module

public import CFSG.Quasithin.Background.F1Borel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] {L1 L2 S : Subgroup G}

theorem bigB_le_normalizer_of_hyp111 (h : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
  sup_le (sup_le ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer) h.h1.borel_le)
    h.h1.normalizes

theorem Hyp111.pCoreOf_le_pCoreOf_vertex [Finite G] (h : Hyp111 L1 L2 S) :
    pCoreOf 2 L1 ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L1).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L1)
      ((bigB_le_normalizer_of_hyp111 h).trans (normalizer_le_normalizer_pCoreOf 2 L1)))
    (pCoreOf_isPGroup 2 L1)

end CFSG.Quasithin
