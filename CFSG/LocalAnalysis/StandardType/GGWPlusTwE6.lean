module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Quot
public import CFSG.LocalAnalysis.StandardType.GGWPlusPositionRk
public import CFSG.LocalAnalysis.StandardType.GGWPlusAutomizer
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem ggWPlusTableBRk_twE6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGWPlusTableBRk 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) 6 := by
  intro M _ _ L' E θ hE hP hr6 hZ A M₁ E₁ h hXA hAN hAp hME hEA hCM hAM hAE hpow hh hhp hAh
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  haveI : Finite (MulAut (TwE6Delta.RecipeR K n)) := TwE6Delta.finite_mulAut_recipeR hK
  have hr : 3 ^ 5 ≤ Nat.card (ggLAutImage L' θ E) := by
    simpa using pow_pred_le_card_ggLAutImage hP Nat.prime_three hr6
  have hsc : GGTorusSelfCent 3 (ggLAutImage L' θ E) :=
    ggTorusSelfCent_ggLAutImage hP Nat.prime_three hZ
  have hA : IsElemAbelian 3 (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      TwE6Delta.RecipeI K n := by
    intro a ha
    simp only [ggLAutImage, Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  have hperf : commutator (TwE6Delta.RecipeR K n) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ y
    have hl : l ∈ commutator L' := by rw [hP.1]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem (ggQuotHom θ) hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ggQuotHom_surjective θ), ← commutator_def] at h1
  have hX := ggSolvQuotLeTwo_twE6_three (Eb := ggLAutImage L' θ E) n hn hK h3 hA hI hr hsc hperf
  haveI : ((MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)).range).Normal :=
    ggInnNormal _
  exact wplus_of_automizer Nat.prime_three (by norm_num) _
    (ggLAutImage L' θ E) hX A M₁ E₁ hXA hAN hAp hME hEA hCM hAM hAE hpow h hh hAh

end CFSG.StandardType
