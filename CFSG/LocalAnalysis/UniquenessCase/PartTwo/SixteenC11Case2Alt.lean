module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c11_altSix_pairs :
    ∃ (T₁ : Subgroup (FFModel.altDn 6).Gam) (N : ℕ), IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧
      Odd (S16C11ModelPairs (FFModel.altDn_isActionModel 6) T₁ N).ncard := by
  haveI : Finite (FFModel.altDn 6).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 6)))
  obtain ⟨T₁, N, y₀, a, b, hT, hidx, hF, hTS, h3, hmov⟩ := s16c11_altSix_forced
  refine ⟨T₁, N, hT, hidx, ?_⟩
  have hcard : (S16C11ModelPairs (FFModel.altDn_isActionModel 6) T₁ N).ncard = 1 := by
    unfold S16C11ModelPairs
    exact (congrArg Set.ncard (s16c11_actPairs_eq_forcedPairs hF)).trans
      (s16c11_forcedPairs_ncard_eq_one hTS h3 hmov)
  rw [hcard]
  exact odd_one

theorem s16c11_altSeven_pairs :
    ∃ (T₁ : Subgroup (FFModel.altDn 7).Gam) (N : ℕ), IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧
      Odd (S16C11ModelPairs (FFModel.altDn_isActionModel 7) T₁ N).ncard := by
  haveI : Finite (FFModel.altDn 7).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  obtain ⟨T₁, N, y₀, a, b, hT, hidx, hF, hcard⟩ := s16c11_altSeven_forced
  refine ⟨T₁, N, hT, hidx, ?_⟩
  have h3 : (S16C11ModelPairs (FFModel.altDn_isActionModel 7) T₁ N).ncard = 3 := by
    unfold S16C11ModelPairs
    exact (congrArg Set.ncard (s16c11_actPairs_eq_forcedPairs hF)).trans hcard
  rw [h3]
  exact ⟨1, rfl⟩

theorem s16c11_altEight_pairs :
    ∃ (T₁ : Subgroup (FFModel.altDn 8).Gam) (N : ℕ), IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧
      Odd (S16C11ModelPairs (FFModel.altDn_isActionModel 8) T₁ N).ncard := by
  haveI : Finite (FFModel.altDn 8).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 8)))
  obtain ⟨T₁, N, y₀, a, b, hT, hidx, hF, hTS, h3, hmov⟩ := s16c11_altEight_forced
  refine ⟨T₁, N, hT, hidx, ?_⟩
  have hcard : (S16C11ModelPairs (FFModel.altDn_isActionModel 8) T₁ N).ncard = 1 := by
    unfold S16C11ModelPairs
    exact (congrArg Set.ncard (s16c11_actPairs_eq_forcedPairs hF)).trans
      (s16c11_forcedPairs_ncard_eq_one hTS h3 hmov)
  rw [hcard]
  exact odd_one

theorem s16c11_rf3Odd_of_alternatingNatural {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) (h : AlternatingNatural L J ⊥ n) :
    S16C11RF3Odd L J := by
  rcases hn with rfl | rfl | rfl
  · obtain ⟨T₁, N, hT, hidx, hodd⟩ := s16c11_altSix_pairs
    exact s16c11_rf3Odd_of_modelPairs (FFC.altDn_faithful (by norm_num))
      (FFModel.altDn_isActionModel 6) h hT hidx hodd
  · obtain ⟨T₁, N, hT, hidx, hodd⟩ := s16c11_altSeven_pairs
    exact s16c11_rf3Odd_of_modelPairs (FFC.altDn_faithful (by norm_num))
      (FFModel.altDn_isActionModel 7) h hT hidx hodd
  · obtain ⟨T₁, N, hT, hidx, hodd⟩ := s16c11_altEight_pairs
    exact s16c11_rf3Odd_of_modelPairs (FFC.altDn_faithful (by norm_num))
      (FFModel.altDn_isActionModel 8) h hT hidx hodd

theorem s16c11_rf3_of_alt {W : Type} [CommGroup W] [Finite W] {L L₀ : Subgroup (MulAut W)}
    {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) (hLL₀ : L ≤ L₀) (hS : IsSym ↥L₀ n)
    (hA : IsAlt ↥L n) (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (h : AlternatingNatural L J ⊥ n) :
    S16C11RF3 L₀ J :=
  s16c11_rf3_of_rf3Odd hLL₀
    (s16c11_map_conj_eq_of_card_two_mul hLL₀
      (s16e_card_eq_two_mul_of_isSym_isAlt (by omega) hS hA))
    hJ (s16c11_rf3Odd_of_alternatingNatural hn h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
