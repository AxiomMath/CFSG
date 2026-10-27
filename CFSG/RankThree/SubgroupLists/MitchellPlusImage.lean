module

public import CFSG.RankThree.SubgroupLists.SymplecticTwoRotations

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K : Type} [Field K]

theorem eq_zero_of_plusBlock_eq_zero (h2 : (2 : K) ≠ 0) {N W : Matrix V₄ V₄ K} {q : K}
    (hq : q ≠ 0) (hNT : N * tStdMat = tStdMat * N) (hWT : W * tStdMat = -(tStdMat * W))
    (hNW : N * W = W * N) (hWW : W * W = q • 1) (hN : plusBlock N = 0) : N = 0 := by
  have h00 : N (Sum.inl 0) (Sum.inl 0) = 0 := by
    simpa [plusBlock] using congrFun (congrFun hN 0) 0
  have h01 : N (Sum.inl 0) (Sum.inr 0) = 0 := by
    simpa [plusBlock] using congrFun (congrFun hN 0) 1
  have h10 : N (Sum.inr 0) (Sum.inl 0) = 0 := by
    simpa [plusBlock] using congrFun (congrFun hN 1) 0
  have h11 : N (Sum.inr 0) (Sum.inr 0) = 0 := by
    simpa [plusBlock] using congrFun (congrFun hN 1) 1
  have hz : ∀ i j : V₄, stdSign i ≠ (stdSign j : K) → N i j = 0 := fun i j h =>
    entry_eq_zero_of_commute_tStd h2 hNT h
  have hne := one_ne_neg_one_of_two h2
  have hp : N * (1 + tStdMat) = 0 := by
    ext i j
    simp only [Matrix.mul_add, Matrix.mul_one, tStdMat, Matrix.mul_diagonal, Matrix.add_apply,
      Matrix.zero_apply]
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [stdSign, h00, h01, h10, h11] <;>
      first
      | (rw [hz _ _ (by simp [stdSign]; exact hne)]; simp)
      | (rw [hz _ _ (by simp [stdSign]; exact hne.symm)]; simp)
  have hWP : W * (1 + tStdMat) = (1 - tStdMat) * W := by
    rw [Matrix.mul_add, Matrix.mul_one, hWT, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg]
  have hm : N * (1 - tStdMat) * W = 0 := by
    rw [Matrix.mul_assoc, ← hWP, ← Matrix.mul_assoc, hNW, Matrix.mul_assoc, hp, Matrix.mul_zero]
  have hm' : N * (1 - tStdMat) = 0 := by
    have := congrArg (· * W) hm
    simp only [Matrix.zero_mul, Matrix.mul_assoc, hWW, Matrix.mul_smul, Matrix.mul_one] at this
    exact (smul_eq_zero.mp this).resolve_left hq
  have h2N : (2 : K) • N = 0 := by
    have : N * (1 + tStdMat) + N * (1 - tStdMat) = (2 : K) • N := by
      rw [← Matrix.mul_add, show (1 + tStdMat) + (1 - tStdMat) = (2 : K) • (1 : Matrix V₄ V₄ K)
        by module, Matrix.mul_smul, Matrix.mul_one]
    rw [← this, hp, hm', add_zero]
  exact (smul_eq_zero.mp h2N).resolve_left h2

theorem mul_comm_of_anticomm {R : Type*} [Ring R] {T D E : R} (hD : T * D = -(D * T))
    (hE : T * E = -(E * T)) : T * (D * E) = D * E * T := by
  rw [← mul_assoc, hD, neg_mul, mul_assoc, hE, mul_neg, neg_neg, ← mul_assoc]

theorem plusImage_mono (h2 : (2 : K) ≠ 0) {G₁ G₂ : Subgroup (GL V₄ K)} (h : G₁ ≤ G₂) :
    plusImage h2 G₁ ≤ plusImage h2 G₂ :=
  Subgroup.map_mono (Subgroup.map_mono fun _ hg => h hg)

theorem exists_mem_of_mem_plusImage (h2 : (2 : K) ≠ 0) {H : Subgroup (GL V₄ K)}
    {z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K} (hz : z ∈ plusImage h2 H) :
    ∃ (h : GL V₄ K) (hH : h ∈ H) (hC : h ∈ stdCent K), z = (plusBar h2 hH hC).1 := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
  exact ⟨b.1, hb, b.2, rfl⟩

section Finite

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem mul_eq_or_eq_neg_of_plusBar_commute (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) {x y : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (hyG : y ∈ G) (hyC : y ∈ stdCent K)
    {W : Matrix V₄ V₄ K} {q : K} (hq : q ≠ 0) (hWT : W * tStdMat = -(tStdMat * W))
    (hWW : W * W = q • 1) (hxW : W * ⟪x⟫ = ⟪x⟫ * W) (hyW : W * ⟪y⟫ = ⟪y⟫ * W)
    (hcomm : plusBar (two_ne_zero_of_charP hp2) hxG hxC *
      plusBar (two_ne_zero_of_charP hp2) hyG hyC = plusBar (two_ne_zero_of_charP hp2) hyG hyC *
      plusBar (two_ne_zero_of_charP hp2) hxG hxC) :
    x * y = y * x ∨ x * y = -(y * x) := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  obtain ⟨c, hc⟩ : ∃ c : GL V₄ K, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcG : c ∈ G := hc ▸ Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ hxG hyG) (Subgroup.inv_mem _ hxG)) (Subgroup.inv_mem _ hyG)
  have hcC : c ∈ stdCent K := hc ▸ mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC))
    (inv_mem hyC)
  obtain ⟨σ, hσ, hσc⟩ : ∃ σ : K, (σ = 1 ∨ σ = -1) ∧
      plusBlock ⟪c⟫ = σ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have hcp : plusBlock ⟪c⟫ = 1 ∨ plusBlock ⟪c⟫ = -1 := by
      refine (plusBar_eq_one_iff h2 hcG hcC).mp ?_
      have e : plusBar h2 hcG hcC = plusBar h2 hxG hxC * plusBar h2 hyG hyC *
          (plusBar h2 hxG hxC)⁻¹ * (plusBar h2 hyG hyC)⁻¹ := by
        subst hc
        rw [plusBar_inv hp2 hU0 hneg, plusBar_inv hp2 hU0 hneg, plusBar_mul, plusBar_mul,
          plusBar_mul]
      rw [e, hcomm]
      group
    rcases hcp with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_smul, h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul, h]⟩
  have hcW : W * ⟪c⟫ = ⟪c⟫ * W := by
    have hcx : Commute W ⟪x⟫ := hxW
    have hcy : Commute W ⟪y⟫ := hyW
    rw [hc, Units.val_mul, Units.val_mul, Units.val_mul]
    exact (((hcx.mul_right hcy).mul_right hcx.units_inv_right).mul_right
      hcy.units_inv_right).eq
  have hN0 : ⟪c⟫ - σ • (1 : Matrix V₄ V₄ K) = 0 := by
    refine eq_zero_of_plusBlock_eq_zero h2 hq ?_ hWT ?_ hWW ?_
    · simp only [Matrix.sub_mul, Matrix.mul_sub, (mem_stdCent.mp hcC).2, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, ← hcW, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · rw [plusBlock_sub, plusBlock_smul, plusBlock_one, hσc, sub_self]
  have hxy : x * y = c * (y * x) := by rw [hc]; group
  have hcσ : c = 1 ∨ c = -1 := by
    rcases hσ with rfl | rfl
    · exact Or.inl (Units.ext (by rw [sub_eq_zero.mp hN0, one_smul, Units.val_one]))
    · exact Or.inr (Units.ext (by
        rw [sub_eq_zero.mp hN0, neg_one_smul, Units.val_neg, Units.val_one]))
  rcases hcσ with h | h
  · left
    rw [hxy, h, one_mul]
  · right
    rw [hxy, h, neg_one_mul]

theorem plusBlock_eq_or_neg_of_plusBar_eq (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) {x y : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (hyG : y ∈ G) (hyC : y ∈ stdCent K)
    (h : plusBar (two_ne_zero_of_charP hp2) hxG hxC = plusBar (two_ne_zero_of_charP hp2) hyG hyC) :
    plusBlock ⟪x⟫ = plusBlock ⟪y⟫ ∨ plusBlock ⟪x⟫ = -plusBlock ⟪y⟫ := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have e : plusBar h2 (G.mul_mem hxG (G.inv_mem hyG)) (mul_mem hxC (inv_mem hyC)) =
      plusBar h2 hxG hxC * (plusBar h2 hyG hyC)⁻¹ := by
    rw [plusBar_inv hp2 hU0 hneg, plusBar_mul]
  have hz : plusBar h2 (G.mul_mem hxG (G.inv_mem hyG)) (mul_mem hxC (inv_mem hyC)) = 1 := by
    rw [e, h, mul_inv_cancel]
  have hxy := plusBlock_mul h2 (mem_stdCent.mp (mul_mem hxC (inv_mem hyC))).2
    (mem_stdCent.mp hyC).2
  rw [← Units.val_mul, inv_mul_cancel_right] at hxy
  rcases (plusBar_eq_one_iff h2 _ _).mp hz with h1 | h1
  · left
    rw [hxy, h1, one_mul]
  · right
    rw [hxy, h1, neg_mul, one_mul]

end Finite

end CFSG.RankThree.SubgroupLists
