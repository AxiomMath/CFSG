module

public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Quot
public import CFSG.LocalAnalysis.StandardType.GGWPlusAutomizer
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem ggWPlusTableB_E6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGWPlusTableB 3 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  intro M _ _ L' E θ hE hP hZ A M₁ E₁ h hXA hAN hAp hME hEA hCM hAM hAE hpow hh hhp hAh
  haveI : CharP K 2 := charP_two_of_card hK
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have hL : GGTorusLift 3 5 (TableBExc.RecipeGroup .E6 K) :=
    TableBExc.ggTorusLift_E6_three hpK
  have hr : 3 ^ 5 ≤ Nat.card (ggLAutImage L' θ E) :=
    pow_le_card_ggLAutImage hP Nat.prime_three hL
  have hsc : GGTorusSelfCent 3 (ggLAutImage L' θ E) :=
    ggTorusSelfCent_ggLAutImage hP Nat.prime_three hZ
  have hA : IsElemAbelian 3 (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆
      TableBExc.RecipeID .E6 K := by
    intro a ha
    simp only [ggLAutImage, Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  have hperf : commutator (TableBExc.RecipeGroup .E6 K) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ y
    have hl : l ∈ commutator L' := by rw [hP.1]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem (ggQuotHom θ) hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ggQuotHom_surjective θ), ← commutator_def] at h1
  have hX := ggSolvQuotLeTwo_E6_three (Eb := ggLAutImage L' θ E) n hn hK h3 hA hI hr hsc hperf
  haveI : ((MulAut.conj : TableBExc.RecipeGroup .E6 K →*
      MulAut (TableBExc.RecipeGroup .E6 K)).range).Normal :=
    ggInnNormal _
  haveI : Finite (TableBExc.RecipeGroup .E6 K) := TableBExc.finite_recipeGroup .E6 K
  haveI : Finite (MulAut (TableBExc.RecipeGroup .E6 K)) :=
    Finite.of_injective (fun f : MulAut (TableBExc.RecipeGroup .E6 K) =>
      (f : TableBExc.RecipeGroup .E6 K → TableBExc.RecipeGroup .E6 K))
      DFunLike.coe_injective
  exact wplus_of_automizer Nat.prime_three (by norm_num) _
    (ggLAutImage L' θ E) hX A M₁ E₁ hXA hAN hAp hME hEA hCM hAM hAE hpow h hh hAh

end CFSG.StandardType
