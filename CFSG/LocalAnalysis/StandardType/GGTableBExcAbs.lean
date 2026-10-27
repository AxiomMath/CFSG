module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggTableBAbsorptionAt_of_subset_inn {R : Type} [Group R] {p : ℕ}
    {I : Set (MulAut R)} (h : I ⊆ (MulAut.conj : R →* MulAut R).range) :
    GGTableBAbsorptionAt p I := by
  intro M _ _ L' E θ hE hpos i hi
  obtain ⟨ρ, hρ⟩ := h hi
  exact ⟨ρ, 1, by rw [hρ, mul_one], fun e => Commute.one_left _⟩

theorem absorption_exc
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBExcInnRow p lab ∨ GGL48TBExcTwoRow p lab) :
    LargeEvenLabelAll lab fun _ _ I _ => GGTableBAbsorptionAt p I := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases hrow with ⟨htag, -⟩ | ⟨htag, hn1, -⟩
  · rcases htag with h | h | h <;> dsimp only at h <;> subst h
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ hK => by
        have := charP_two_of_card hK
        exact ggTableBAbsorptionAt_of_subset_inn
          (chevIDImage_subset_inn_of_top (τ := .E7) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
            TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K)))) hQ
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ _ => ggTableBAbsorptionAt_of_subset_inn
        (chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩))) hQ
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ _ => ggTableBAbsorptionAt_of_subset_inn
        (chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩))) hQ
  · rcases htag with h | h | h | h <;> dsimp only at h <;> subst h
    · subst hn1
      exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ hK => by
        have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two
          (K := K) (by simpa using hK)
        exact ggTableBAbsorptionAt_of_subset_inn (chevIDImage_subset_inn_of_subsingleton _)) hQ
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ hK => by
        have := charP_two_of_card hK
        exact ggTableBAbsorptionAt_of_subset_inn
          (chevIDImage_subset_inn_of_top (τ := .E7) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
            TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K)))) hQ
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ _ => ggTableBAbsorptionAt_of_subset_inn
        (chevIDImage_subset_inn_of_top (τ := .E8) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩))) hQ
    · exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I) (fun K _ _ _ => ggTableBAbsorptionAt_of_subset_inn
        (chevIDImage_subset_inn_of_top (τ := .F4) (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K
          TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩))) hQ

end CFSG.StandardType
