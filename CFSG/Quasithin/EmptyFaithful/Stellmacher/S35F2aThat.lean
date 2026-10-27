module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aBase

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem That_std_eq :
    That S5Syl = Subgroup.closure ({swap 0 2, swap 1 3} : Set (Perm (Fin 5))) := That_std

theorem That_cj_std (r : Perm (Fin 5)) :
    That (cj r S5Syl) =
      Subgroup.closure ({r * swap 0 2 * r⁻¹, r * swap 1 3 * r⁻¹} : Set (Perm (Fin 5))) := by
  rw [← cj_That, That_std_eq, cj_closure, Set.image_pair]

@[expose] def genT (r : Perm (Fin 5)) : Finset (Perm (Fin 5)) :=
  {swap 0 2, swap 1 3, r * swap 0 2 * r⁻¹, r * swap 1 3 * r⁻¹}

theorem That_sup_std (r : Perm (Fin 5)) :
    That S5Syl ⊔ That (cj r S5Syl) = Subgroup.closure ((genT r : Finset (Perm (Fin 5))) :
      Set (Perm (Fin 5))) := by
  rw [That_std_eq, That_cj_std, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [genT, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert,
    Finset.coe_singleton]
  tauto

theorem mem_That_sup_iff (r : Perm (Fin 5)) (n : ℕ) (hinv : ∀ t ∈ genT r, t⁻¹ ∈ genT r)
    (hfix : ∀ x ∈ ballF (genT r) n, ∀ t ∈ genT r, x * t ∈ ballF (genT r) n)
    (x : Perm (Fin 5)) : x ∈ That S5Syl ⊔ That (cj r S5Syl) ↔ x ∈ ballF (genT r) n := by
  rw [That_sup_std]
  exact Set.ext_iff.mp (closure_eq_ballF (genT r) n hinv hfix) x

private theorem genT_inv_r2 : ∀ t ∈ genT r2, t⁻¹ ∈ genT r2 := by
  unfold genT r2; decide +kernel

private theorem genT_inv_r4 : ∀ t ∈ genT r4, t⁻¹ ∈ genT r4 := by
  unfold genT r4; decide +kernel

private theorem genT_fix_r2 :
    ∀ x ∈ ballF (genT r2) 4, ∀ t ∈ genT r2, x * t ∈ ballF (genT r2) 4 := by
  unfold genT r2; decide +kernel

private theorem genT_fix_r4 :
    ∀ x ∈ ballF (genT r4) 4, ∀ t ∈ genT r4, x * t ∈ ballF (genT r4) 4 := by
  unfold genT r4; decide +kernel

private theorem ball_r2 :
    ballF (genT r2) 4 = Finset.univ.filter (fun x : Perm (Fin 5) => x 4 = 4) := by
  unfold genT r2
  decide +kernel

private theorem card_ball_r4 : (ballF (genT r4) 4).card = 12 := by
  unfold genT r4
  decide +kernel

set_option maxRecDepth 10000 in
theorem That_sup_r2 : That S5Syl ⊔ That (cj r2 S5Syl) = ptStab 4 := by
  ext x
  refine (mem_That_sup_iff r2 4 genT_inv_r2 genT_fix_r2 x).trans ?_
  rw [ball_r2, mem_ptStab]
  simp

set_option maxRecDepth 10000 in
theorem card_That_sup_r4 : Nat.card ↥(That S5Syl ⊔ That (cj r4 S5Syl)) = 12 := by
  have e : ↥(That S5Syl ⊔ That (cj r4 S5Syl)) ≃ ↥(ballF (genT r4) 4) :=
    Equiv.subtypeEquivRight (mem_That_sup_iff r4 4 genT_inv_r4 genT_fix_r4)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_ball_r4]

theorem That_sup_r8 : That S5Syl ⊔ That (cj r8 S5Syl) = ⊤ := by
  have h02 : swap 0 2 ∈ That S5Syl ⊔ That (cj r8 S5Syl) := by
    refine Subgroup.mem_sup_left ?_
    rw [That_std_eq]; exact Subgroup.subset_closure (by simp)
  have h13 : swap 1 3 ∈ That S5Syl ⊔ That (cj r8 S5Syl) := by
    refine Subgroup.mem_sup_left ?_
    rw [That_std_eq]; exact Subgroup.subset_closure (by simp)
  have h02' : r8 * swap 0 2 * r8⁻¹ ∈ That S5Syl ⊔ That (cj r8 S5Syl) := by
    refine Subgroup.mem_sup_right ?_
    rw [That_cj_std]; exact Subgroup.subset_closure (by simp)
  have h13' : r8 * swap 1 3 * r8⁻¹ ∈ That S5Syl ⊔ That (cj r8 S5Syl) := by
    refine Subgroup.mem_sup_right ?_
    rw [That_cj_std]; exact Subgroup.subset_closure (by simp)
  have hT : ∀ t ∈ [swap 0 2, swap 1 3, r8 * swap 0 2 * r8⁻¹, r8 * swap 1 3 * r8⁻¹],
      t ∈ That S5Syl ⊔ That (cj r8 S5Syl) := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  refine eq_top_of_words _ hT [1, 2, 1] [0, 1, 2, 0, 1] [0, 2, 0] [1, 3, 1] ?_ ?_ ?_ ?_ <;>
    unfold evalW r8 <;> decide +kernel

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
