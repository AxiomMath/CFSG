module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Frame
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGTBRowExcFrame
import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
import CFSG.LocalAnalysis.StandardType.GGTBRowF4FrameAux
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenElt
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section F4


theorem card_tbGroup_F4 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TableBF4.RecipeGroup K}
    {A : Subgroup (MulAut L')}
    (hA : GGTorusTBGroup p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) L' ψ A) :
    Nat.card A = p ^ 4 := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, τ, -, Θ, hτ, -, -, -⟩ :=
    exists_weylGenModel hp hp2 (TableBF4.idImage_subset_inn K)
      (TableBF4.center_recipeGroup_eq_bot K)
      (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
        (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all hp hp2)) hψ hker hperf hAe hAI hr h3
  set τ' := (TableBF4.recipeEquiv K).toMonoidHom.comp τ
  have hτ' : Function.Injective τ' := (TableBF4.recipeEquiv K).injective.comp hτ
  have hcard : Nat.card τ'.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hτ').toEquiv.symm).trans (Nat.card_congr Θ.toEquiv)
  have hE : IsElemAbelian p τ'.range :=
    isElemAbelian_range (fun a b => mul_comm a b)
      (fun a => pow_eq_one_of_multiplicative_fin_zmod a) τ'
  rw [← hcard] at hr ⊢
  exact F4AutWeyl.card_eq_pow_four_of_le hp hp2 hE hr

end F4


theorem ggQ2TableBI1FailOn_exc : GGQ2TableBI1FailOn GGQ2TBExcLabel := by
  refine ggQ2TableBI1FailOn_of_frames ?_ ?_
  · rintro ⟨t, r, n⟩ (h | h | h) <;> subst h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · rintro ⟨t, r, n⟩ hlab hq hS
    have hn1 : n = 1 := by
      have hnpos : 1 ≤ n := by simpa using hlab.1
      have hq2 : n < 2 := by simpa only [GGLabQTwo] using hq
      omega
    subst hn1
    rcases hS with ht | ht | ht <;> subst ht
    ·
      refine ⟨Fin 4, inferInstance, inferInstance, CoxeterMatrix.F₄, CartanMatrix.F₄,
        ?_, ?_, ggIntCartan_F₄, SecFiveRootRefl.entries_F₄, SecFiveRootRefl.cartanTree_F₄, ?_, ?_⟩
      · simp only [GGQ2LabelWeyl]
        exact ⟨Equiv.refl _, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))))
      · rw [CartanMatrix.F₄_det]
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        omega
      · intro Q hQ
        dsimp only [LargeEvenRawDatum] at hQ ⊢
        obtain ⟨K, _, _, hK, hQ'⟩ := hQ
        have : CharP K 2 := charP_two_of_card hK
        have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; norm_num
        exact ⟨K, inferInstance, inferInstance, hK, hQ',
          ExcSplitL.ggCenterPrime_recipe_F4 (K := K) Nat.prime_three (by norm_num), 3, 4, le_rfl,
          ggTorusLift_F4Plus Nat.prime_three (by norm_num) hpq,
          ggTorusWeylFrameW_of_coordFrameElt Nat.prime_three (by norm_num)
            (TableBF4.idImage_subset_inn K) (TableBF4.center_recipeGroup_eq_bot K)
            (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
              (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all Nat.prime_three (by norm_num)))
            (ggTorusCoordFrameElt_of_mulEquiv (TableBF4.recipeEquiv K)
              (ggWTF4_coordFrameElt_adjointF4 (K := K) Nat.prime_three (by norm_num))),
          fun L' _ _ ψ A hTB => by
            rw [Fintype.card_fin]
            exact card_tbGroup_F4 Nat.prime_three (by norm_num) hTB⟩
    ·
      refine ⟨Fin 7, inferInstance, inferInstance, CoxeterMatrix.E₇, CartanMatrix.E 7,
        ?_, ggIsWeylMatrix_E7, ggIntCartan_E₇, SecFiveRootRefl.entries_E 7,
        SecFiveRootRefl.cartanTree_E 7 (by norm_num), ?_, ?_⟩
      · simp only [GGQ2LabelWeyl]
        exact ⟨Equiv.refl _, rfl⟩
      · rw [CartanMatrix.E_det (by norm_num)]
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        omega
      · have hc : LargeEvenLabelAll ⟨.E7, r, 1⟩ fun R _ _ _ => GGCenterPrime 3 R := by
          intro Q hQ
          dsimp only [LargeEvenRawDatum] at hQ ⊢
          obtain ⟨K, _, _, hK, hQ'⟩ := hQ
          have : CharP K 2 := charP_two_of_card hK
          exact ⟨K, inferInstance, inferInstance, hK, hQ',
            ExcSplitL.ggCenterPrime_recipe_E7 (f := 1) le_rfl hK Nat.prime_three (by norm_num)⟩
        refine LargeEvenLabelAll.mono (fun R _ I F h => ?_)
          (largeEvenLabelAll_and (largeEvenLabelAll_and hc
            (largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by norm_num)
              (lab := ⟨.E7, r, 1⟩) ⟨Or.inl rfl, by norm_num⟩))
            (ggNEE_largeEvenLabelAll_model_excPlus Nat.prime_three (by norm_num)
              (lab := ⟨.E7, r, 1⟩) (Or.inl rfl) (by norm_num)))
        obtain ⟨⟨hcp, hlift⟩, hmod⟩ := h
        refine ⟨hcp, 6, 6, Nat.le_succ 6, hlift, ?_, fun L' _ _ ψ A hTB => ?_⟩
        · rw [FrameRoute.coxeterE7_eq]
          exact ggTorusWeylFrameW_of_excPlusModelSCr (τ := .E7) Nat.prime_three (by norm_num)
            (MulEquiv.refl _) (fun _ => rfl) hmod
        · obtain ⟨Φ, -, -, -⟩ := hmod L' ψ A hTB
          calc Nat.card ↥A = Nat.card (Fin 7 → ZMod 3) := Nat.card_congr Φ.toEquiv
            _ = 3 ^ Fintype.card (Fin 7) := by
              rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, Fintype.card_fin]
    ·
      refine ⟨Fin 8, inferInstance, inferInstance, CoxeterMatrix.E₈, CartanMatrix.E 8,
        ?_, ggIsWeylMatrix_E8, ggIntCartan_E₈, SecFiveRootRefl.entries_E 8,
        SecFiveRootRefl.cartanTree_E 8 (by norm_num), ?_, ?_⟩
      · simp only [GGQ2LabelWeyl]
        exact ⟨Equiv.refl _, rfl⟩
      · rw [CartanMatrix.E_det (by norm_num)]
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        omega
      · have hc : LargeEvenLabelAll ⟨.E8, r, 1⟩ fun R _ _ _ => GGCenterPrime 3 R := by
          intro Q hQ
          dsimp only [LargeEvenRawDatum] at hQ ⊢
          obtain ⟨K, _, _, hK, hQ'⟩ := hQ
          have : CharP K 2 := charP_two_of_card hK
          exact ⟨K, inferInstance, inferInstance, hK, hQ',
            ExcSplitL.ggCenterPrime_recipe_E8 (K := K) Nat.prime_three (by norm_num)⟩
        refine LargeEvenLabelAll.mono (fun R _ I F h => ?_)
          (largeEvenLabelAll_and (largeEvenLabelAll_and hc
            (largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by norm_num)
              (lab := ⟨.E8, r, 1⟩) ⟨Or.inr (Or.inl rfl), by norm_num⟩))
            (ggNEE_largeEvenLabelAll_model_excPlus Nat.prime_three (by norm_num)
              (lab := ⟨.E8, r, 1⟩) (Or.inr rfl) (by norm_num)))
        obtain ⟨⟨hcp, hlift⟩, hmod⟩ := h
        refine ⟨hcp, 7, 7, Nat.le_succ 7, hlift, ?_, fun L' _ _ ψ A hTB => ?_⟩
        · rw [FrameRoute.coxeterE8_eq]
          exact ggTorusWeylFrameW_of_excPlusModelSCr (τ := .E8) Nat.prime_three (by norm_num)
            (MulEquiv.refl _) (fun _ => rfl) hmod
        · obtain ⟨Φ, -, -, -⟩ := hmod L' ψ A hTB
          calc Nat.card ↥A = Nat.card (Fin 8 → ZMod 3) := Nat.card_congr Φ.toEquiv
            _ = 3 ^ Fintype.card (Fin 8) := by
              rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, Fintype.card_fin]

end CFSG.StandardType

end
