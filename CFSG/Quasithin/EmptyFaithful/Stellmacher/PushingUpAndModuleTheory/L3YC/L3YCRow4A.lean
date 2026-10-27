module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4AHyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

namespace Stellmacher.PU.L3YC

theorem blk4_mul (y y' : Fin 3 → ZMod 2) (A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    blk4 y A * blk4 y' A' = blk4 (y' + y ᵥ* A') (A * A') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

theorem blk4'_mul (A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x x' : Fin 3 → ZMod 2) :
    blk4' A x * blk4' A' x' = blk4' (A * A') (A *ᵥ x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4', Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

theorem blk4_one : blk4 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4]

theorem blk4'_one : blk4' 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4']

theorem eq_blk4_of_blockForm1 {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : BlockForm 1 3 M) :
    M = blk4 (fun i : Fin 3 => M 0 i.succ) (blkAt 1 3 (by norm_num) M) := by
  obtain ⟨h1, -, h3, -⟩ := hM
  have e00 : M 0 0 = 1 := by simpa using h3 0 0 (by decide) (by decide)
  have e10 : M 1 0 = 0 := h1 1 0 (by decide) (by decide)
  have e20 : M 2 0 = 0 := h1 2 0 (by decide) (by decide)
  have e30 : M 3 0 = 0 := h1 3 0 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4, blkAt_apply, *]

theorem eq_blk4'_of_blockForm0 {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : BlockForm 0 3 M) :
    M = blk4' (blkAt 0 3 (by norm_num) M) (fun i : Fin 3 => M i.castSucc 3) := by
  obtain ⟨-, h2, -, h4⟩ := hM
  have e30 : M 3 0 = 0 := h2 3 0 (by decide) (by decide)
  have e31 : M 3 1 = 0 := h2 3 1 (by decide) (by decide)
  have e32 : M 3 2 = 0 := h2 3 2 (by decide) (by decide)
  have e33 : M 3 3 = 1 := by simpa using h4 3 3 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | simp [blk4', blkAt_apply, *]

theorem transvection_cross4 (l : Fin 3) :
    (1 + Matrix.single (0 : Fin 4) l.succ (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4 (Pi.single l 1) 1 := by
  ext a b
  fin_cases l <;> fin_cases a <;> fin_cases b <;> simp [blk4, Matrix.single_apply]

theorem transvection_cross4' (k : Fin 3) :
    (1 + Matrix.single k.castSucc (3 : Fin 4) (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4' 1 (Pi.single k 1) := by
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [blk4', Matrix.single_apply]

section Gen

variable {B : Type} [Group B] (θ : B →* SpecialLinearGroup (Fin 4) (ZMod 2))

theorem generate_V4pt (T : Subgroup B)
    (hT : ∀ (k l : Fin 4) (hc : IsCross 1 3 k l), ∃ p ∈ T,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) (z : Fin 3 → ZMod 2) :
    ∃ n ∈ T, ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4 z 1 := by
  classical
  let P : (Fin 3 → ZMod 2) → Prop := fun z => ∃ n ∈ T,
    ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = blk4 z 1
  have h0 : P 0 := ⟨1, T.one_mem, by
    rw [map_one, Matrix.SpecialLinearGroup.coe_one]; exact blk4_one.symm⟩
  have hadd : ∀ z z', P z → P z' → P (z + z') := by
    rintro z z' ⟨n, hn, hnZ⟩ ⟨n', hn', hnZ'⟩
    refine ⟨n * n', T.mul_mem hn hn', ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hnZ, hnZ', blk4_mul]
    simp [add_comm]
  have hs : ∀ (l : Fin 3) (t : ZMod 2), P (Pi.single l t) := by
    intro l t
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · simpa using h0
    · have hc : IsCross 1 3 (0 : Fin 4) l.succ := Or.inl ⟨by simp, by simp, by simp; omega⟩
      obtain ⟨p, hp, hpθ⟩ := hT _ _ hc
      refine ⟨p, hp, ?_⟩
      rw [hpθ, CFSG.LinearGroups.coe_transvection]
      exact transvection_cross4 l
  rw [← Finset.univ_sum_single z]
  exact Finset.sum_induction _ P hadd h0 fun l _ => hs l (z l)

theorem generate_V4hyp (T : Subgroup B)
    (hT : ∀ (k l : Fin 4) (hc : IsCross 0 3 k l), ∃ p ∈ T,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) (x : Fin 3 → ZMod 2) :
    ∃ n ∈ T, ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4' 1 x := by
  classical
  let P : (Fin 3 → ZMod 2) → Prop := fun x => ∃ n ∈ T,
    ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = blk4' 1 x
  have h0 : P 0 := ⟨1, T.one_mem, by
    rw [map_one, Matrix.SpecialLinearGroup.coe_one]; exact blk4'_one.symm⟩
  have hadd : ∀ x x', P x → P x' → P (x + x') := by
    rintro x x' ⟨n, hn, hnZ⟩ ⟨n', hn', hnZ'⟩
    refine ⟨n * n', T.mul_mem hn hn', ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hnZ, hnZ', blk4'_mul]
    simp [add_comm]
  have hs : ∀ (k : Fin 3) (t : ZMod 2), P (Pi.single k t) := by
    intro k t
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · simpa using h0
    · have hc : IsCross 0 3 k.castSucc (3 : Fin 4) := Or.inr ⟨by simp, by simp, by simp⟩
      obtain ⟨p, hp, hpθ⟩ := hT _ _ hc
      refine ⟨p, hp, ?_⟩
      rw [hpθ, CFSG.LinearGroups.coe_transvection]
      exact transvection_cross4' k
  rw [← Finset.univ_sum_single x]
  exact Finset.sum_induction _ P hadd h0 fun k _ => hs k (x k)

theorem add_add_self_fn (p q : Fin 3 → ZMod 2) : p + q + q = p := by
  ext i
  simp [add_assoc, Heis.zmod2_add_self]

theorem ptStab_eq_blk4SL (M : SpecialLinearGroup (Fin 4) (ZMod 2)) (hM : M ∈ ptStab) :
    ∃ (y : Fin 3 → ZMod 2) (A : SpecialLinearGroup (Fin 3) (ZMod 2)), M = blk4SL y A := by
  have hs := ptStab_shape M hM
  have hdet : (Matrix.of fun i j : Fin 3 =>
      (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ).det = 1 := by
    have h2 := congrArg Matrix.det hs
    rw [det_blk4] at h2
    rw [← h2]
    exact M.2
  exact ⟨fun i : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 i.succ, ⟨_, hdet⟩,
    Subtype.ext hs⟩

theorem hypStab_eq_blk4'SL (M : SpecialLinearGroup (Fin 4) (ZMod 2)) (hM : M ∈ hypStab) :
    ∃ (A : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2), M = blk4'SL A x := by
  have hs := hypStab_shape M hM
  have hdet : (Matrix.of fun i j : Fin 3 =>
      (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc j.castSucc).det = 1 := by
    have h2 := congrArg Matrix.det hs
    rw [det_blk4'] at h2
    rw [← h2]
    exact M.2
  exact ⟨⟨_, hdet⟩, fun i : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc 3,
    Subtype.ext hs⟩

theorem theta_eq_pt (α : B →* SpecialLinearGroup (Fin 3) (ZMod 2))
    (hαs : Function.Surjective α)
    (hblk : ∀ x : B, blkAt 1 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 1 3 ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hV : ∀ z : Fin 3 → ZMod 2, ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        blk4 z 1) :
    (⊤ : Subgroup B).map θ = ptStab := by
  apply le_antisymm
  · rintro _ ⟨x, -, rfl⟩
    have hx := eq_blk4_of_blockForm1 (hblk x).2
    rw [mem_ptStab_iff, hx]
    intro i
    fin_cases i <;> simp [blk4]
  · intro M hM
    obtain ⟨y, A, rfl⟩ := ptStab_eq_blk4SL M hM
    obtain ⟨x, hx⟩ := hαs A
    have hxs0 := eq_blk4_of_blockForm1 (hblk x).2
    rw [(hblk x).1, hx] at hxs0
    obtain ⟨y', hxs⟩ : ∃ y' : Fin 3 → ZMod 2,
        ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          blk4 y' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := ⟨_, hxs0⟩
    obtain ⟨n, hn⟩ := hV (y + y')
    refine ⟨x * n, Subgroup.mem_top _, Subtype.ext ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hn, hxs, blk4SL_coe, blk4_mul]
    simp only [Matrix.vecMul_one, mul_one, add_add_self_fn]

theorem theta_eq_hyp (α : B →* SpecialLinearGroup (Fin 3) (ZMod 2))
    (hαs : Function.Surjective α)
    (hblk : ∀ x : B, blkAt 0 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hV : ∀ z : Fin 3 → ZMod 2, ∃ n : B,
      ((θ n : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        blk4' 1 z) :
    (⊤ : Subgroup B).map θ = hypStab := by
  apply le_antisymm
  · rintro _ ⟨x, -, rfl⟩
    have hx := eq_blk4'_of_blockForm0 (hblk x).2
    rw [mem_hypStab_iff, hx]
    intro j
    fin_cases j <;> simp [blk4']
  · intro M hM
    obtain ⟨A, x₀, rfl⟩ := hypStab_eq_blk4'SL M hM
    obtain ⟨x, hx⟩ := hαs A
    have hxs0 := eq_blk4'_of_blockForm0 (hblk x).2
    rw [(hblk x).1, hx] at hxs0
    obtain ⟨x', hxs⟩ : ∃ x' : Fin 3 → ZMod 2,
        ((θ x : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          blk4' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) x' := ⟨_, hxs0⟩
    obtain ⟨n, hn⟩ := hV (((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (x₀ + x'))
    refine ⟨x * n, Subgroup.mem_top _, Subtype.ext ?_⟩
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hn, hxs, blk4'SL_coe, blk4'_mul]
    have h1 : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        (((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          (x₀ + x')) = x₀ + x' := by
      have := sl_mulVec_inv_self (A⁻¹) (x₀ + x')
      rwa [inv_inv] at this
    rw [h1, add_add_self_fn, mul_one]

end Gen

end Stellmacher.PU.L3YC

end CFSG.Quasithin
