module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.S151

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem not_isFFModule_of_lemma1518 {T Mc M : Subgroup G} (hV : IsElemAbelian 2 (V154 T Mc M))
    (h : Lemma1518Concl T Mc M) :
    ¬ @IsFFModule (V154 T Mc M) (commGroupOfElemAbelian hV) (autOn M (V154 T Mc M)) := by
  have hq : qOn M (V154 T Mc M) = 2 := by
    rcases h with h | h
    · exact h.2
    · exact h.2.2
  have hq' : @qOf ↥(V154 T Mc M) (commGroupOfElemAbelian hV) inferInstance
      (autOn M (V154 T Mc M)) = 2 := by
    simp only [qOn, hV, ↓reduceDIte] at hq
    exact hq
  intro hFF
  have hsq : ∀ v : ↥(V154 T Mc M), v ^ 2 = 1 := fun v => Subtype.ext (by
    simpa using F7.isElemAbelian_pow_eq_one hV v.2)
  have h1 := ((@B1_4_5 ↥(V154 T Mc M) (commGroupOfElemAbelian hV) inferInstance hsq
    (autOn M (V154 T Mc M))).out 1 3).mp hFF
  rw [hq'] at h1
  exact absurd h1 (by norm_num)

end CFSG.Quasithin.S151
