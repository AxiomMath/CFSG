module

public import CFSG.Quasithin.EmptyFaithful.S151cOneMain
public import CFSG.Quasithin.EmptyFaithful.S151cOrbI
public import CFSG.Quasithin.EmptyFaithful.S151cCaseii

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Casei151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

open Classical in
theorem caseI_main (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hcase : ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥) (hCE1 : Nat.card V ≠ 4)
    (hCE2 : ¬ IsOFourPlusAct X) : CaseI151c X Tb (Jhat X) := by
  obtain ⟨K, hK, hJK, hf⟩ := hcase
  rcases hK with ⟨L, hL, hnorm, hKL⟩ | ⟨L, hL, L₂, hL₂, hne, ⟨x₂, hx₂, e₂⟩, horb, hKL⟩
  ·
    have hJL : Jhat X = L := hJK.trans hKL
    have hLu : ∀ L' ∈ I, L' = L := fun L' hL' =>
      block_eq_of_le hI hL' hL (hJL ▸ block_le_J hI hL')
    have B := oneBlock_of_single h hr hr2 hI hL hLu hf
    exact oneBlock_cases B hCE1
  ·
    have hJ : Jhat X = L ⊔ L₂ := hJK.trans hKL
    obtain ⟨hr2', ⟨p, hp, hA6⟩, hn, hgen, hA⟩ :=
      twoOrbit_cases h hr hr2 hI hL hL₂ hne hx₂ e₂ horb hJ hf hCE2
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hA6⟩))))), hn, hgen,
      Or.inl ⟨?_, ?_⟩⟩
    · rw [hr] ; subst hr2' ; rfl
    · obtain ⟨A, hAq, hA2⟩ := hA
      subst hr2'
      exact qOf_eq_of_qstar_card_two h.sq hr hAq hA2

open Classical in
theorem refined1512 (h : Setting151c X Tb Xc) (hCE1 : Nat.card V ≠ 4) (hCE2 : ¬ IsOFourPlusAct X) :
    Case6Aut X Tb Xc (Jhat X) ∨ CaseI151c X Tb (Jhat X) := by
  obtain ⟨r, hr, hr2⟩ := exists_rat_qhat h
  obtain ⟨I, hI⟩ := exists_isBlocks216 hr2 (Jhat X) (Jhat_compat hr hr2).1
    (Jhat_compat hr hr2).2
  by_cases hcase : ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥
  · exact Or.inr (caseI_main h hr hr2 hI hcase hCE1 hCE2)
  · exact Or.inl (caseii_main h hr hr2 hI hcase)

end Casei151c

end CFSG.Quasithin
