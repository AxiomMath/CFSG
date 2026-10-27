module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

theorem inndiagGroup_eq_adjointGroup_of_card_two
    {τ : Tag} {K : Type} [Field K] (hK2 : Nat.card K = 2) :
    inndiagGroup τ K = adjointGroup τ K := by
  refine le_antisymm ?_ adjointGroup_le_inndiagGroup
  rintro w ⟨b, j, hj, rfl⟩
  have hb : b = 1 := by
    funext i
    have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hunits).1
    exact Subsingleton.elim _ _
  rw [hb, rootDiagUnit_one, one_mul]
  exact hj

theorem inndiagConj_injective_of_four_le
    {τ : Tag} {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) :
    Function.Injective (inndiagConj τ K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show (w : ModGL τ K) = 1
  refine eq_one_of_commute_adjointGroup hK4 w.2 fun h hh => ?_
  have := congrArg (fun α : MulAut (adjointGroup τ K) => ((α ⟨h, hh⟩ : adjointGroup τ K) :
    ModGL τ K)) (MonoidHom.mem_ker.1 hw)
  simp only [coe_inndiagConj, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem inndiagConj_injective_of_card_eq_two_pow
    {τ : Tag} {K : Type} [Field K] [Finite K] {n : ℕ} (hcard : Nat.card K = 2 ^ n) :
    Function.Injective (inndiagConj τ K) := by
  by_cases hK4 : 4 ≤ Nat.card K
  · exact inndiagConj_injective_of_four_le hK4
  have h2 : Nat.card K = 2 := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ 2 ^ n := by rw [← hcard, h]
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzC : (z : ModGL τ K) ∈ adjointGroup τ K := by
    rw [← inndiagGroup_eq_adjointGroup_of_card_two h2]
    exact z.2
  have hzz : (⟨z, hzC⟩ : adjointGroup τ K) ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := congrArg (fun α : MulAut (adjointGroup τ K) => ((α g : adjointGroup τ K) :
      ModGL τ K)) (MonoidHom.mem_ker.1 hz)
    simp only [coe_inndiagConj, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzz
  have hz1 : (z : ModGL τ K) = 1 := congrArg (fun x : adjointGroup τ K => (x : ModGL τ K)) hzz
  exact Subtype.ext hz1

end RecipeExcLang

end CFSG.StandardType

end
