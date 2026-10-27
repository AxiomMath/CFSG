module

public import CFSG.Quasithin.Background.C31Steps

public section

namespace CFSG.Quasithin.C31

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem asc31Statement_of (hBasic : C31BasicStep G) (hSpor : C31SporStep G)
    (hNonLie : C31NonLieStep G) (hLie : C31LieStep G)
    (hC : ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
      CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K)) :
    ASC31Statement G := by
  intro H R M L V K h hK
  have hb := hBasic H R M L V K h hK
  have hnorm : ((conjClosure L M).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_conjClosure L M)
  have hLie' := hLie H R M L V K h hK hb
  have hNL := hNonLie H R M L V K h hK hb
  have hcase : L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
        C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
        C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
        C31Case10 H R M L V K) := by
    have hlie : C31Lie2Types (↥K ⧸ Subgroup.center ↥K) → L = conjClosure L M ∧
        (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
          C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
          C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
          C31Case10 H R M L V K) := fun ht => by
      obtain ⟨hL, c1 | c2 | c10⟩ := hLie' ht
      · exact ⟨hL, Or.inl c1⟩
      · exact ⟨hL, Or.inr (Or.inl c2)⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          c10))))))))⟩
    rcases hC H R M L V K h hK with ⟨n, hn5, hn8, he⟩ | hodd | h2 | h45 | ⟨s, hs, he⟩
    ·
      have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl | rfl
      · exact hlie (Or.inl he)
      · exact hlie (Or.inr (Or.inl he))
      · exact absurd (Or.inl he) hNL
      · exact hlie (Or.inr (Or.inr (Or.inl he)))
    · exact absurd (Or.inr hodd) hNL
    · exact hlie (Or.inr (Or.inr (Or.inr (Or.inl h2))))
    · exact hlie (Or.inr (Or.inr (Or.inr (Or.inr h45))))
    · obtain ⟨hL, c3 | c4 | c5 | c6 | c7 | c8 | c9⟩ := hSpor H R M L V K h hK hb s hs he
      · exact ⟨hL, Or.inr (Or.inr (Or.inl c3))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inl c4)))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c5))))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c6)))))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c7))))))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c8)))))))⟩
      · exact ⟨hL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl c9))))))))⟩
  exact ⟨hcase.1, hnorm, hb.1, hb.2.1, hb.2.2, hcase.2⟩

end CFSG.Quasithin.C31
