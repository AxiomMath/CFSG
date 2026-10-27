module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem not_isMaximalLocal_of_lt {G : Type} [Group G] {T K K' : Subgroup G} (hlt : K < K')
    (hK' : quasithinIsMaximalLocal T K') : ¬ quasithinIsMaximalLocal T K := fun hK =>
  hlt.ne (hK.2 K' hK'.1 hlt.le).symm

theorem stmt5_2_9_of (h527 : Stmt5_2_7) (h528 : Stmt5_2_8) : Stmt5_2_9 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have h2n : 2 ≤ n := hyp.two_le
  obtain ⟨htype, -, -⟩ := h527 G T M L V H B D L₂ n hyp
  rcases h528 G T M L V H B D L₂ n hyp with hK | ⟨hA, K', hlt, hK', -⟩
  · rcases htype with (h | h | h | h | h) | ⟨m, hm, h2, hU⟩ | ⟨h4, hU⟩
    · exact Or.inl ⟨n, h2n, Or.inl ⟨h, hK⟩⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inl ⟨h, hK⟩)⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inl ⟨h, hK⟩))⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hK⟩)))⟩
    · exact Or.inl ⟨n, h2n, Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hK⟩)))⟩
    · exact Or.inr (Or.inl ⟨m, hm, h2, hU, hK⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hU, hK⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hA, not_isMaximalLocal_of_lt hlt hK'⟩))

end CFSG.Quasithin.H13
