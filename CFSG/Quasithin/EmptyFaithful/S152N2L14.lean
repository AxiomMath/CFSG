module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithful.S152N2Lin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N2

variable {G : Type} [Group G] [Finite G]

theorem qOf_eq_two_of_lemma1518 {T Mc M : Subgroup G} (hV : IsElemAbelian 2 (V154 T Mc M))
    (h : Lemma1518Concl T Mc M) :
    @qOf ↥(V154 T Mc M) (commGroupOfElemAbelian hV) inferInstance (autOn M (V154 T Mc M)) = 2 := by
  have hq : qOn M (V154 T Mc M) = 2 := by
    rcases h with h | h
    · exact h.2
    · exact h.2.2
  simp only [qOn, hV, ↓reduceDIte] at hq
  exact hq

end CFSG.Quasithin
