module

public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.SimplyLacedCover
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem iform_eq_sum_single_basis (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ j, x j * iform (Pi.single j 1) y := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [iform_finset_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Pi.single j (x j) : Fin τ.rank → ℤ) = x j • Pi.single j 1 := by
    ext k
    by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  rw [e, iform_smul_left]

theorem exists_isRoot_sub_single_of_two_le_height (hτ : ∀ i, τ.symmetrizer i i = 1)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hh : 2 ≤ height α) :
    ∃ j, IsRoot τ (α - Pi.single j 1) ∧ 0 < height (α - Pi.single j 1) := by
  have hpos : 0 < height α := by omega
  have hnn : ∀ j, 0 ≤ α j := (IsRoot.height_pos_iff hα).1 hpos
  have hexp : (2 : ℤ) = ∑ j, α j * iform (Pi.single j 1) α := by
    rw [← iform_self_eq_two hτ hα]
    exact iform_eq_sum_single_basis α α
  have hex : ∃ j, 0 < α j * iform (Pi.single j 1) α := by
    by_contra h
    push Not at h
    have hle : (∑ j, α j * iform (Pi.single j 1) α) ≤ 0 :=
      Finset.sum_nonpos fun j _ => h j
    omega
  obtain ⟨j, hj⟩ := hex
  have haj0 : α j ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hj
    exact lt_irrefl 0 hj
  have haj : 0 < α j := lt_of_le_of_ne (hnn j) (Ne.symm haj0)
  have hij : 0 < iform (Pi.single j 1) α := pos_of_mul_pos_right hj (le_of_lt haj)
  have hne : α ≠ Pi.single j 1 := by
    intro h
    rw [h, height_single] at hh
    omega
  have hne' : α ≠ -Pi.single j 1 := by
    intro h
    rw [h, height_neg, height_single] at hpos
    omega
  have hpos' : 0 < iform α (Pi.single j 1) := by rwa [iform_comm]
  refine ⟨j, isRoot_sub_of_iform_pos hα (isRoot_single τ j) hne hpos', ?_⟩
  rw [height_sub, height_single]
  omega

theorem isRoot_eq_single_or_exists_add (hτ : ∀ i, τ.symmetrizer i i = 1)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hpos : 0 < height α) :
    (∃ j, α = Pi.single j 1) ∨
      ∃ a b : Fin τ.rank → ℤ, IsRoot τ a ∧ IsRoot τ b ∧ 0 < height a ∧ 0 < height b ∧
        α = a + b := by
  by_cases h1 : height α = 1
  · left
    have hnn : ∀ j, 0 ≤ α j := (IsRoot.height_pos_iff hα).1 hpos
    have hex : ∃ j, α j ≠ 0 := by
      by_contra h
      push Not at h
      have hzero : height α = 0 := Finset.sum_eq_zero fun j _ => h j
      omega
    obtain ⟨j, hj0⟩ := hex
    have h1le : 1 ≤ α j := by
      have : 0 < α j := lt_of_le_of_ne (hnn j) (Ne.symm hj0)
      omega
    have hle : α j ≤ height α := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    have haj : α j = 1 := by omega
    refine ⟨j, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk
      rw [haj, Pi.single_eq_same]
    · have hk0 : α k = 0 := by
        by_contra hkne
        have hkpos : 0 < α k := lt_of_le_of_ne (hnn k) (Ne.symm hkne)
        have hle' : α k + α j ≤ height α := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg
            (s := ({k, j} : Finset (Fin τ.rank))) (t := Finset.univ) (f := α)
            (by simp) (fun i _ _ => hnn i)
          rwa [Finset.sum_pair hk] at hsub
        omega
      rw [hk0, Pi.single_eq_of_ne hk]
  · right
    have h2 : 2 ≤ height α := by omega
    obtain ⟨j, hjroot, hjpos⟩ := exists_isRoot_sub_single_of_two_le_height hτ hα h2
    exact ⟨α - Pi.single j 1, Pi.single j 1, hjroot, isRoot_single τ j, hjpos,
      by rw [height_single]; exact one_pos, by rw [sub_add_cancel]⟩

end CFSG.StandardType

end
