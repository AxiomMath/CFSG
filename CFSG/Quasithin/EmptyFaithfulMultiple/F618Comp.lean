module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompThree
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompGraph
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompM12
public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Props
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompAlt

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple


namespace F618Comp

theorem socle_of_caseOriented {D : Type} [Group D] [Finite D] {H₁ H₂ : Subgroup D}
    (hT : ∃ S : Sylow 2 D, (S : Subgroup D) = H₁ ⊓ H₂) (h : F6.IsF618CaseOrientedCat H₁ H₂) :
    Socle D := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨e⟩, -⟩ := h
    obtain ⟨S, hS⟩ := hT
    exact Or.inl (not_isComponent_of_card_sylow S (by rw [hS, Nat.card_congr e.toEquiv]; simp))
  ·
    have := isSolvable_of_caseTwo h
    exact socle_of_isSolvable
  ·
    exact socle_of_caseThree hT h
  ·
    obtain ⟨⟨p, -, hp24, hL⟩, -⟩ := h
    exact socle_of_isL2_mod_eight hL (by rw [pow_one]; rcases hp24 with h | h <;> omega)
      (by rw [pow_one]; rcases hp24 with h | h <;> omega)
  ·
    obtain ⟨⟨q, hq, hq24, hP⟩, -⟩ := h
    exact socle_of_isPGL2 hq hq24 hP
  ·
    obtain ⟨hA | ⟨p, e, -, -, -, hq, hL⟩, -⟩ := h
    · exact socle_of_isHatAlt hA (by norm_num) (notSL2_of_isHatAlt hA (Or.inl rfl))
    · exact socle_of_isL2_mod_sixteen hL hq
  ·
    obtain ⟨e | hA, -⟩ := h
    · exact Socle.of_mulEquiv e.some socle_alternating_seven
    · exact socle_of_isHatAlt hA (by norm_num) (notSL2_of_isHatAlt hA (Or.inr rfl))
  ·
    obtain ⟨hA | ⟨p, -, hp8, hL⟩, -⟩ := h
    · exact socle_of_isHatSym hA (Or.inl rfl)
    · exact socle_of_isL2FieldExtCat hp8 hL
  ·
    obtain ⟨e | hA | ⟨p, -, hp24, hL⟩, -⟩ := h
    · exact Socle.of_mulEquiv e.some socle_perm_seven
    · exact socle_of_isHatSym hA (Or.inr rfl)
    · exact socle_of_isL2FieldExtCat (by rcases hp24 with h | h <;> omega) hL
  ·
    obtain ⟨⟨p, hp8, hL⟩, -⟩ := h
    exact socle_of_isSLEps3 (by rcases hp8 with h | h <;> omega) hL
  ·
    obtain ⟨⟨p, hp8, hL⟩, -⟩ := h
    exact socle_of_isSLEps3GraphExt hp8 hL
  ·
    obtain ⟨⟨e⟩, -⟩ := h
    exact Socle.of_mulEquiv e socle_m12
  ·
    obtain ⟨⟨e⟩, -⟩ := h
    exact Socle.of_mulEquiv e socle_autM12

end F618Comp

open F618Comp in
theorem f618ComponentInspection_holds : F618ComponentInspection := by
  intro D _ _ G₁ G₂ hT _ hcase M hM
  have hS : ∃ S : Sylow 2 D, (S : Subgroup D) = G₁ ⊓ G₂ := hT.sylow
  have hS' : ∃ S : Sylow 2 D, (S : Subgroup D) = G₂ ⊓ G₁ := inf_comm G₁ G₂ ▸ hT.sylow
  have hsoc : Socle D := by
    rcases hcase with h | h
    · exact socle_of_caseOriented hS h
    · exact socle_of_caseOriented hS' h
  exact conclusion_of_socle hsoc hM

end CFSG.Quasithin.EmptyFaithfulMultiple
