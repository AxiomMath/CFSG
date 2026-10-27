module

public import CFSG.Quasithin.Vol2.Ch3B513NCase245

public section

namespace CFSG.Quasithin.B513N

@[expose] def Case1 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), ¬ Group.IsSolvable ↥G → G ≠ ⊥ → B53Hyp G → B56Case1 G →
      HasGood G

@[expose] def Case3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), ¬ Group.IsSolvable ↥G → G ≠ ⊥ → B53Hyp G → B56Case3 G →
      HasGood G

theorem core_of_cases (hB56 : AsB56) (h1 : Case1) (h3 : Case3) : Core := by
  intro W _ _ hW G hsolv hne hB53
  rcases hB56 W hW G hne hB53 with h | h | h | h | h
  · exact h1 W hW G hsolv hne hB53 h
  · exact absurd (isSolvable_of_case2 h) hsolv
  · exact h3 W hW G hsolv hne hB53 h
  · exact hasGood_of_case4 hW h
  · exact hasGood_of_case5 hW h

theorem b513Nonsolvable_of_cases (hB56 : AsB56) (h1 : Case1) (h3 : Case3) : B513Nonsolvable :=
  b513Nonsolvable_of_core (core_of_cases hB56 h1 h3)

end CFSG.Quasithin.B513N
