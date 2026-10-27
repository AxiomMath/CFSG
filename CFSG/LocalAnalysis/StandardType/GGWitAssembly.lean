module

public import CFSG.LocalAnalysis.StandardType.GGWitSlpmCr
public import CFSG.LocalAnalysis.StandardType.GGWitMon
public import CFSG.LocalAnalysis.StandardType.GGWitOrth
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClass
public import CFSG.LocalAnalysis.StandardType.GGWitExcAbstract
public import CFSG.LocalAnalysis.StandardType.GGWitExcModel

public section

namespace CFSG.StandardType.ZS

theorem ggWitnessInput_holds : WitnessInput := by
  intro p _ U _ _ _ A hp2 hd hrg hai hfam
  have hp : p.Prime := Fact.out
  cases hfam with
  | weyl h => exact Or.inl h
  | slpm hA =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    intro r hr hrefl
    exact Or.inl (wit_slpm_cr hp2 hd A hA r hr hrefl)
  | orth Q hQ hA =>
    by_cases hsmall : Module.finrank (ZMod p) U = 3 ∨
        (p = 3 ∧ (Module.finrank (ZMod p) U = 4 ∨ Module.finrank (ZMod p) U = 5))
    · rcases wit_orth_small hp hp2 Q hQ hA hsmall with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hdne3 : Module.finrank (ZMod p) U ≠ 3 := by
        intro h3; exact hsmall (Or.inl h3)
      by_cases hp3 : p = 3
      · have hdne4 : Module.finrank (ZMod p) U ≠ 4 := by
          intro h4; exact hsmall (Or.inr ⟨hp3, Or.inl h4⟩)
        have hdne5 : Module.finrank (ZMod p) U ≠ 5 := by
          intro h5; exact hsmall (Or.inr ⟨hp3, Or.inr h5⟩)
        have hd6 : 6 ≤ Module.finrank (ZMod p) U := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        intro r hr hrefl
        exact Or.inr (wit_orth_l51 hp hp2 hp3 hd6 Q hQ hA r hr hrefl)
      · have hp5 : 5 ≤ p := by
          have h2 : 2 ≤ p := hp.two_le
          have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
          omega
        have hd4 : 4 ≤ Module.finrank (ZMod p) U := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        intro r hr hrefl
        exact Or.inl (wit_orth_cr hp hp2 hp5 hd4 Q hQ hA r hr hrefl)
  | orthClass Q c hQ hc hA =>
    by_cases hp3 : p = 3
    · by_cases hd3 : Module.finrank (ZMod p) U = 3
      · exact Or.inl (wit_orthClass_three_three hp hp2 Q hQ c hc hA hai hp3 hd3)
      · by_cases hd4 : Module.finrank (ZMod p) U = 4
        · exact Or.inl (wit_orthClass_three_four hp hp2 Q hQ c hc hA hai hp3 hd4)
        · by_cases hd5 : Module.finrank (ZMod p) U = 5
          · rcases wit_orthClass_three_five hp hp2 Q hQ c hc hA hai hp3 hd5 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                (fun r hr hrefl => Or.inr (h r hr hrefl)))))
          · have hd6 : 6 ≤ Module.finrank (ZMod p) U := by omega
            refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            intro r hr hrefl
            exact Or.inr (wit_orthClass_l51 hp hp2 Q hQ c hc hA hp3 hd6 r hr hrefl)
    · by_cases hp5 : p = 5
      · by_cases hd3 : Module.finrank (ZMod p) U = 3
        · rcases wit_orthClass_five_three hp hp2 Q hQ c hc hA hai hp5 hd3 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
        · have hd4 : 4 ≤ Module.finrank (ZMod p) U := by omega
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          intro r hr hrefl
          exact Or.inl (wit_orthClass_cr hp hp2 Q hQ c hc hA (by omega : 5 ≤ p) hd4 r hr hrefl)
      · have hp7 : 7 ≤ p := by
          have h2 : 2 ≤ p := hp.two_le
          have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
          have h6 : p ≠ 6 := by rintro rfl; norm_num at hp
          omega
        by_cases hd3 : Module.finrank (ZMod p) U = 3
        · rcases wit_orthClass_dim3 hp hp2 Q hQ c hc hA hp7 hd3 with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (fun r hr hrefl => Or.inl (h r hr hrefl)))))
        · have hd4 : 4 ≤ Module.finrank (ZMod p) U := by omega
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          intro r hr hrefl
          exact Or.inl (wit_orthClass_cr hp hp2 Q hQ c hc hA (by omega : 5 ≤ p) hd4 r hr hrefl)
  | gmmn f i₀ i₁ ζ m h01 hm hζ hA =>
    refine Or.inr (Or.inl ?_)
    rw [hA]
    exact wit_gmmn_mon f (by
      have h := Module.finrank_eq_card_basis f
      rw [h, Fintype.card_fin] at hd
      exact hd) i₀ i₁ ζ m h01 hm hζ
  | g2mmn f i₀ i₁ ζ m h01 hm hζ hA =>
    refine Or.inr (Or.inl ?_)
    rw [hA]
    exact wit_g2mmn_mon f (by
      have h := Module.finrank_eq_card_basis f
      rw [h, Fintype.card_fin] at hd
      exact hd) i₀ i₁ ζ m h01 hm hζ
  | exc k hadm hdeg hcard hcen hD hone hmod =>
    by_cases hk : k.needsModel
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      intro r hr hrefl
      exact Or.inr (wit_exc_model k hk hone (hmod hk) r hr hrefl)
    · rcases wit_exc_abstract hp hp2 hai k hk hadm hdeg hcard hcen hD hone with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (fun r hr hrefl => Or.inl (h r hr hrefl)))))
  | h4 _ _ _ _ hD hone =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (fun r hr hrefl => Or.inl (witCR_of_dMax (by decide) hD hone r hr hrefl)))))

end CFSG.StandardType.ZS

end
