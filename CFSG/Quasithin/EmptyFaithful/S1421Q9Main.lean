module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9E
public import CFSG.Quasithin.EmptyFaithful.S1421Q9F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem lemma14209Used_of_shape
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h128One : Lemma128One) (h128Two : Lemma128Two) (h128Four : Lemma128Four)
    (hL34 : Q9.L34Maximal)
    (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G) (st : Setting1427 T M H K1)
    (sh : Shape1428 T H K1) (hlt : S1421.sOf T K1 < T) :
    ∃ Kc ∈ cComp (mcOf T), K1 ≤ Kc ∧ oTwoUpper H ≤ Kc ⊔ T ∧
      ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
        Kc ≤ K1 ⊔ T1 ∨ 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) := by
  rcases sh.cases with ⟨hK1K, -⟩ | ⟨hK1, -⟩ | ⟨hK, -, hs3⟩
  · exfalso
    rcases st.notation_.index with ⟨-, hTN⟩ | ⟨hlt', -⟩
    · exact hlt.ne (le_antisymm hlt.le fun t ht => ⟨ht, hTN ht⟩)
    · exact hlt'.ne hK1K
  · exact Q9.case2 h37 h38 h39 h128One h128Two st hK1 hlt
  · exact Q9.case3 h37 h38 h39 h128Four hL34 st hK hs3

end CFSG.Quasithin
