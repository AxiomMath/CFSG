module

public import CFSG.Quasithin.Vol2.Ch3Sec3Wreath
public import CFSG.Quasithin.Background.F7Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin

section PermOf

variable {K X : Type} [Group K] (act : K →* Equiv.Perm X) {n : ℕ} (D : Fin n → X)
  (hD : Function.Injective D) (hinv : ∀ (k : K) (i : Fin n), ∃ j, act k (D i) = D j)

@[expose] noncomputable def idx (k : K) (i : Fin n) : Fin n := Classical.choose (hinv k i)

theorem idx_spec (k : K) (i : Fin n) : act k (D i) = D (idx act D hinv k i) :=
  Classical.choose_spec (hinv k i)

include hD in
theorem idx_eq_iff (k : K) (i j : Fin n) : idx act D hinv k i = j ↔ act k (D i) = D j := by
  constructor
  · rintro rfl
    exact idx_spec act D hinv k i
  · intro h
    exact hD ((idx_spec act D hinv k i).symm.trans h)

include hD in
theorem idx_mul (k k' : K) (i : Fin n) :
    idx act D hinv (k * k') i = idx act D hinv k (idx act D hinv k' i) := by
  rw [idx_eq_iff act D hD, map_mul, Equiv.Perm.mul_apply, idx_spec act D hinv k' i,
    idx_spec act D hinv k]

include hD in
theorem idx_one (i : Fin n) : idx act D hinv (1 : K) i = i := by
  rw [idx_eq_iff act D hD, map_one, Equiv.Perm.one_apply]

@[expose] noncomputable def permOf : K →* Equiv.Perm (Fin n) where
  toFun k :=
    { toFun := idx act D hinv k
      invFun := idx act D hinv k⁻¹
      left_inv := fun i => by rw [← idx_mul act D hD, inv_mul_cancel, idx_one act D hD]
      right_inv := fun i => by rw [← idx_mul act D hD, mul_inv_cancel, idx_one act D hD] }
  map_one' := by
    ext i
    exact congrArg Fin.val (idx_one act D hD hinv i)
  map_mul' k k' := by
    ext i
    exact congrArg Fin.val (idx_mul act D hD hinv k k' i)

theorem permOf_apply_eq_iff (k : K) (i j : Fin n) :
    permOf act D hD hinv k i = j ↔ act k (D i) = D j :=
  idx_eq_iff act D hD hinv k i j

end PermOf

section Conj

variable {A : Type} [Group A]

@[expose] def conjPerm : A →* Equiv.Perm (Subgroup A) where
  toFun k :=
    { toFun := conjSub k
      invFun := conjSub k⁻¹
      left_inv := fun D => by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      right_inv := fun D => by rw [← conjSub_mul, mul_inv_cancel, conjSub_one] }
  map_one' := Equiv.ext fun D => conjSub_one D
  map_mul' k k' := Equiv.ext fun D => conjSub_mul k k' D

end Conj

@[expose] def BlockPres (σ : Equiv.Perm (Fin 6)) : Prop :=
  (∀ i : Fin 6, (i : ℕ) < 3 → ((σ i : ℕ) < 3 ↔ (σ 0 : ℕ) < 3))

instance : DecidablePred BlockPres := fun σ => by unfold BlockPres; infer_instance

theorem blockPres_check : ∀ σ : Equiv.Perm (Fin 6), BlockPres σ →
    ∃ l ∈ Wreath.words, Wreath.wordProd l = σ := by
  decide +kernel

theorem blockPres_gen : ∀ k : Fin 3, BlockPres (Wreath.gen k) := by
  decide +kernel

private theorem blockPres_other : ∀ σ : Equiv.Perm (Fin 6), BlockPres σ →
    ∀ j : Fin 6, 3 ≤ (j : ℕ) → ((σ j : ℕ) < 3 ↔ ¬ (σ 0 : ℕ) < 3) := by
  decide +kernel

theorem blockPres_mul_check : ∀ σ τ : Equiv.Perm (Fin 6), BlockPres σ → BlockPres τ →
    BlockPres (σ * τ) := by
  intro σ τ hσ hτ i hi
  simp only [Equiv.Perm.mul_apply]
  by_cases h0 : ((τ 0 : Fin 6) : ℕ) < 3
  · have hi' : ((τ i : Fin 6) : ℕ) < 3 := (hτ i hi).2 h0
    rw [hσ _ hi', hσ _ h0]
  · have hi' : ¬ ((τ i : Fin 6) : ℕ) < 3 := fun h => h0 ((hτ i hi).1 h)
    rw [blockPres_other σ hσ _ (Nat.le_of_not_lt hi'),
      blockPres_other σ hσ _ (Nat.le_of_not_lt h0)]

theorem mem_wreathS3Z2_iff (σ : Equiv.Perm (Fin 6)) : σ ∈ wreathS3Z2 ↔ BlockPres σ := by
  constructor
  · intro h
    refine Subgroup.closure_induction (p := fun x _ => BlockPres x) ?_ ?_ ?_ ?_ h
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact blockPres_gen 0
      · exact blockPres_gen 1
      · exact blockPres_gen 2
    · decide +kernel
    · intro x y _ _ hx hy
      exact blockPres_mul_check x y hx hy
    · intro x _ hx
      have : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [← mul_left_cancel_iff (a := x), mul_inv_cancel, ← pow_succ',
          Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [this]
      induction (orderOf x - 1) with
      | zero => rw [pow_zero]; decide +kernel
      | succ m ih => rw [pow_succ]; exact blockPres_mul_check _ _ ih hx
  · intro h
    obtain ⟨l, -, rfl⟩ := blockPres_check σ h
    exact Wreath.wordProd_mem l

end CFSG.Quasithin.H13.Ins314
