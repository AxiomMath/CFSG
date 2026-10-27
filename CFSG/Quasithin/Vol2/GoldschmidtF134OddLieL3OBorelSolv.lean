module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelLevi
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem nontrivial_sl2 : Nontrivial SL(2, K) := by
  refine ⟨⟨SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1, 1, fun h => ?_⟩⟩
  have := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [SpecialLinearGroup.transvection_coe] at this

theorem not_isSolvable_of_levi (hK : 4 ≤ Nat.card K) {M : Subgroup SL(3, K)}
    (f : SL(2, K) →* SL(3, K)) (hf : Function.Injective f)
    (h01 : ∀ c : K, f (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) ∈ M)
    (h10 : ∀ c : K, f (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) ∈ M) :
    ¬ Group.IsSolvable M := by
  intro hM
  have hle : ∀ x : SL(2, K), f x ∈ M := by
    have h : (⊤ : Subgroup SL(2, K)) ≤ M.comap f := by
      rw [← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K),
        Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      change f _ ∈ M
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h01 c
      · exact h10 c
      · exact absurd rfl hij
    exact fun x => h (Subgroup.mem_top x)
  have hg : Function.Injective (f.codRestrict M hle) := fun a b h => hf (congrArg Subtype.val h)
  have hsolv : Group.IsSolvable SL(2, K) := Group.isSolvable_of_isSolvable_injective hg
  have := nontrivial_sl2 (K := K)
  have : Group.IsPerfect SL(2, K) := CFSG.LinearGroups.special_linear_isPerfect (by norm_num)
    (Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four hK))
  exact Group.IsPerfect.not_isSolvable SL(2, K) hsolv

theorem isSolvable_comap_proj {n : ℕ} {H : Subgroup (projectiveSL n K)}
    (hH : Group.IsSolvable H) : Group.IsSolvable (H.comap (proj n K)) := by
  have hZM : scalars n K ≤ H.comap (proj n K) := fun z hz => by
    rw [Subgroup.mem_comap, proj_eq_one_iff.2 hz]
    exact H.one_mem
  have hZ : Group.IsSolvable (scalars n K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (scalars_le_center n K)) (Subgroup.inclusion_injective _)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hZM)
    (((proj n K).comp (H.comap (proj n K)).subtype).codRestrict H fun x => x.2) ?_
  intro x hx
  have hx1 : proj n K x = 1 := congrArg Subtype.val hx
  exact ⟨⟨x.1, proj_eq_one_iff.1 hx1⟩, rfl⟩

theorem reflection_one_notMem (hK : 4 ≤ Nat.card K) {M : Subgroup SL(3, K)}
    (hU : unitriangular 3 K ≤ M) (hM : Group.IsSolvable M) :
    reflection 3 K 1 (by norm_num) (by norm_num) ∉ M := by
  intro hr
  refine not_isSolvable_of_levi hK leviLow leviLow_injective (fun c => ?_) (fun c => ?_) hM
  · rw [leviLow_transvection_zero_one]
    exact hU (transvection_mem_unitriangular (show (0 : Fin 3) < 1 by decide) c)
  · rw [leviLow_transvection_one_zero, ← reflection_one_conj c]
    exact M.mul_mem (M.mul_mem hr
      (hU (transvection_mem_unitriangular (show (0 : Fin 3) < 1 by decide) (-c)))) (M.inv_mem hr)

theorem reflection_two_notMem (hK : 4 ≤ Nat.card K) {M : Subgroup SL(3, K)}
    (hU : unitriangular 3 K ≤ M) (hM : Group.IsSolvable M) :
    reflection 3 K 2 (by norm_num) (by norm_num) ∉ M := by
  intro hr
  refine not_isSolvable_of_levi hK leviHigh leviHigh_injective (fun c => ?_) (fun c => ?_) hM
  · rw [leviHigh_transvection_zero_one]
    exact hU (transvection_mem_unitriangular (show (1 : Fin 3) < 2 by decide) c)
  · rw [leviHigh_transvection_one_zero, ← reflection_two_conj c]
    exact M.mul_mem (M.mul_mem hr
      (hU (transvection_mem_unitriangular (show (1 : Fin 3) < 2 by decide) (-c)))) (M.inv_mem hr)

end CFSG.Quasithin.H13.NQCore.L3Odd
