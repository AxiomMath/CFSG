module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

@[expose] def AsB45Gt1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → ((1 : ℚ) : WithTop ℚ) < qhatOf G →
      qhatOf G ≤ ((2 : ℚ) : WithTop ℚ) → AsB45Table G L ∨ AsB45Part3 G L

theorem isFFModule_of_qhatOf_le_one {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} (h : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)) : IsFFModule G := by
  have h3 : kq G 3 ≤ ((1 : ℚ) : WithTop ℚ) := h
  obtain ⟨A, hA, -, hr⟩ := kq_le_iff.1 h3
  exact (isFFModule_iff hV).2 ⟨A, hA, hr⟩

theorem asB45_of_b42 (h42 : AsB42) (h : AsB45Gt1) : AsB45 := by
  intro V _ _ hV G L hG hq
  by_cases h1 : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)
  · obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender (isFFModule_of_qhatOf_le_one hV h1)
    exact Or.inl ⟨h1, ⟨A, hA⟩, fun A' hA' => h42 V hV G L hG A' hA'⟩
  · rcases h V hV G L hG (not_le.1 h1) hq with ht | h3
    · exact Or.inr (Or.inl ⟨not_le.1 h1, ht⟩)
    · exact Or.inr (Or.inr h3)

theorem asB45Gt1_of_b45 (h : AsB45) : AsB45Gt1 := by
  intro V _ _ hV G L hG h1 hq
  rcases h V hV G L hG hq with ⟨h1', -, -⟩ | ⟨-, ht⟩ | h3
  · exact absurd h1 (not_lt.2 h1')
  · exact Or.inl ht
  · exact Or.inr h3

end CFSG.Quasithin
