module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Solvable

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem Config15418.exists_of_three {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (H : Hyp15418 G T) (h15 : Stmt15415 G T) {Y : Subgroup G} (hY : IsYFamily T Y)
    (h3 : (pCoreOf 2 Y).relIndex Y = 3) : ∃ c : Config15418 G T, c.Y = Y := by
  obtain ⟨M₁, hM₁, hYM₁⟩ := hY.exists_inM
  obtain ⟨Ma, Mb, hne, hMa, hMb, hCa, hCb⟩ := H.hyp.two_centralizer_maximal
  have hTC := le_centralizer_omegaOneCenter T
  obtain ⟨M₂, hM₂, hM₂ne⟩ : ∃ M₂ : Subgroup G, InM T M₂ ∧ M₂ ≠ M₁ := by
    by_cases h : Ma = M₁
    · exact ⟨Mb, ⟨hMb, hTC.trans hCb⟩, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨Ma, ⟨hMa, hTC.trans hCa⟩, h⟩
  obtain ⟨⟨X, hX, hXM₂⟩, hall⟩ := H.h12 M₂ hM₂
  obtain ⟨-, -, -, ⟨s, hs, hsX, -, -⟩, -, -, h6, -⟩ := hall X hX hXM₂
  have h9 : (pCoreOf 2 X).relIndex X = 9 := by
    rcases hs with rfl | rfl
    · exact absurd (h15 H.hnot M₁ M₂ Y X hM₁ hM₂ hY hYM₁ h3 hX hXM₂ (by simpa using hsX))
        (Ne.symm hM₂ne)
    · simpa using hsX
  rcases concl15412Six_iff.mp h6 with ⟨h3', -⟩ | ⟨-, -, X₁, X₂, hd⟩
  · omega
  · exact ⟨⟨M₁, M₂, Y, X, X₁, X₂, hM₁, hM₂, Ne.symm hM₂ne, hY, hYM₁, h3, hX, hXM₂, hd⟩, rfl⟩

theorem stmt15418_of (hInsp : Inspection15418) {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (h8 : Stmt1548 G T)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (h15 : Stmt15415 G T) (h16 : Stmt15416 G T)
    (h17 : Stmt15417 G T) : Stmt15418 G T := by
  intro hnot Y hY
  have H : Hyp15418 G T := ⟨hyp, hnot, h8, h12, h14, h16, h17⟩
  obtain ⟨M, hM, hYM⟩ := hY.exists_inM
  obtain ⟨-, -, -, ⟨s, hs, hsY, -, -⟩, -⟩ := (h12 M hM).2 Y hY hYM
  rcases hs with rfl | rfl
  · exfalso
    obtain ⟨c, rfl⟩ := Config15418.exists_of_three H h15 hY (by simpa using hsY)
    exact c.false_of_inspection H hInsp
  · simpa using hsY

end CFSG.Quasithin.EmptyFaithfulMultiple
