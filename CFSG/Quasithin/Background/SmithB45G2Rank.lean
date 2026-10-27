module

public import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.Quasithin.B45G2

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2Ten CFSG.Quasithin.B42G2F
open CFSG.QuasithinUnique.Setup.X7
open scoped Kronecker

section Omega

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] def omegaT : Ix3 × Ix3 → F := fun p => formQ F p.1 p.2

omit [CharP F 2] in
theorem toM_omegaT : toM (omegaT F) = formQ F := by
  ext i j
  rfl

omit [CharP F 2] in
theorem formQ_mul_self : formQ F * formQ F = 1 := by
  ext i j
  simp only [Matrix.mul_apply, formQ_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_sum_type]

theorem repQ_mul_formQ_mul_transpose (g : ↥(cayleyGroup F)) :
    repQ g * formQ F * (repQ g)ᵀ = formQ F := by
  set M := repQ g with hM
  have hMi : M * repQ g⁻¹ = 1 := by rw [hM, ← map_mul, mul_inv_cancel, map_one]
  have h1 : repQ g * formQ F * (repQ g)ᵀ * formQ F * M = M := by
    calc repQ g * formQ F * (repQ g)ᵀ * formQ F * M
        = M * formQ F * ((repQ g)ᵀ * formQ F * repQ g) := by
          rw [hM]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [repQ_transpose_formQ, Matrix.mul_assoc, formQ_mul_self, Matrix.mul_one]
  have h2 : repQ g * formQ F * (repQ g)ᵀ * formQ F = 1 := by
    calc repQ g * formQ F * (repQ g)ᵀ * formQ F
        = repQ g * formQ F * (repQ g)ᵀ * formQ F * M * repQ g⁻¹ := by
          rw [Matrix.mul_assoc _ M, hMi, Matrix.mul_one]
      _ = 1 := by rw [h1, hMi]
  set X := repQ g * formQ F * (repQ g)ᵀ with hX
  calc X = X * formQ F * formQ F := by rw [Matrix.mul_assoc X, formQ_mul_self, Matrix.mul_one]
    _ = formQ F := by rw [h2, Matrix.one_mul]

omit [Field F] [CharP F 2] in
theorem toM_injective : Function.Injective (toM : (Ix3 × Ix3 → F) → Matrix Ix3 Ix3 F) := by
  intro T T' h
  funext p
  exact congrFun (congrFun h p.1) p.2

theorem rep2_omegaT (g : ↥(cayleyGroup F)) : (rep2 g).mulVec (omegaT F) = omegaT F := by
  apply toM_injective
  rw [toM_rep2, toM_omegaT, repQ_mul_formQ_mul_transpose]

omit [CharP F 2] in
theorem omegaT_mem_altSub : omegaT F ∈ altSub F := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · change formQ F i j = formQ F j i
    rw [formQ_apply, formQ_apply]
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  · change formQ F i i = 0
    rw [formQ_apply]
    rcases i with i | i <;> fin_cases i <;> simp

theorem contr_omegaT : contr F (omegaT F) = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  change formQ F (.inl 0) (.inr 0) + formQ F (.inl 1) (.inr 1) + formQ F (.inl 2) (.inr 2) = 1
  simp only [formQ_apply, Sum.swap_inl, ↓reduceIte]
  linear_combination h2

theorem sub_smul_omegaT_mem_lieSub {T : Ix3 × Ix3 → F} (hT : T ∈ altSub F) :
    T - contr F T • omegaT F ∈ lieSub F := by
  rw [lieSub_eq_inf]
  refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hT (Submodule.smul_mem _ _ omegaT_mem_altSub),
    LinearMap.mem_ker.mpr ?_⟩
  rw [map_sub, map_smul, contr_omegaT, smul_eq_mul, mul_one, sub_self]

theorem map_altSub_eq_map_lieSub (g : ↥(cayleyGroup F)) :
    (altSub F).map (rep2 g - 1).mulVecLin = (lieSub F).map (rep2 g - 1).mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨T, hT, rfl⟩
    refine ⟨T - contr F T • omegaT F, sub_smul_omegaT_mem_lieSub hT, ?_⟩
    have hω : (rep2 g - 1).mulVec (omegaT F) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, rep2_omegaT, sub_self]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_smul, hω, smul_zero,
      sub_zero]
  · exact Submodule.map_mono lieSub_le_altSub

theorem six_le_rank_repLie [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    6 ≤ (repLie z - 1).rank := by
  have hA := six_le_finrank_altSub_map (repQ z) (repQ_mul_self hz) (two_le_rank_repQ hz hz1)
  have e : rep2 z = repQ z ⊗ₖ repQ z := rfl
  rw [← e, map_altSub_eq_map_lieSub] at hA
  have hpiv := finrank_map_le_rank_pivotRep isPivot_lie z (lieSub F)
    (fun w hw => ⟨fun p => w (lP p), secL_restrict hw⟩)
  have : (repLie z - 1) = (pivotRep isPivot_lie z - 1) := rfl
  rw [this]
  omega

end Omega

section Numerics

theorem prod_sub_four_add_le {ι : Type*} (S : Finset ι) (n : ι → ℕ) (hn : ∀ j ∈ S, 6 ≤ n j) :
    ∏ j ∈ S, (n j - 4) + 6 ^ S.card ≤ ∏ j ∈ S, n j + 2 ^ S.card ∧
      2 ^ S.card ≤ ∏ j ∈ S, (n j - 4) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => hn j (Finset.mem_insert_of_mem hj)
    have hna := hn a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
      pow_succ]
    set A := ∏ j ∈ S, n j
    set B := ∏ j ∈ S, (n j - 4)
    have h26 : 2 ^ S.card ≤ 6 ^ S.card := Nat.pow_le_pow_left (by norm_num) _
    obtain ⟨x, hx⟩ : ∃ x, A = B + x := ⟨A - B, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, n a = y + 6 := ⟨n a - 6, by omega⟩
    have hx' : 6 ^ S.card ≤ x + 2 ^ S.card := by omega
    rw [hx, hy]
    simp only [show y + 6 - 4 = y + 2 by omega]
    constructor
    · nlinarith
    · nlinarith

theorem sixteen_mul_add_le {s : ℕ} (hs : 2 ≤ s) : 16 * s + 2 ^ s ≤ 6 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ, pow_succ]
    generalize 2 ^ s = a at ih ⊢
    generalize 6 ^ s = b at ih ⊢
    omega

end Numerics

section Tensor

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

theorem letter_bounds_two [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1)
    (l : G2L) (hl : l ≠ .one) :
    6 ≤ Fintype.card l.idx ∧ 2 ≤ (l.rep z - 1).rank ∧
      2 * (l.rep z - 1).rank ≤ Fintype.card l.idx := by
  obtain ⟨h6, -, h2⟩ := letter_bounds hz hz1 l hl
  refine ⟨h6, ?_, h2⟩
  cases l
  · exact absurd rfl hl
  · exact two_le_rank_repQ hz hz1
  · exact le_trans (by norm_num) (five_le_rank_repLie hz hz1)
  · exact le_trans (by norm_num) (eight_le_rank_repSt hz hz1)

theorem eight_mul_le_rank_tRep [Finite F] (lab : Fin f → G2L) {z : ↥(cayleyGroup F)}
    (hz : z * z = 1) (hz1 : z ≠ 1) (hs : 2 ≤ (Finset.univ.filter fun j => lab j ≠ .one).card) :
    8 * (Finset.univ.filter fun j => lab j ≠ .one).card ≤ (tRep F k lab z - 1).rank := by
  classical
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  have h := rank_tRep_sub_one k lab hz
  set n : Fin f → ℕ := fun j => Fintype.card (lab j).idx
  set m : Fin f → ℕ := fun j => Fintype.card (lab j).idx - 2 * ((lab j).rep z - 1).rank
  have hout : ∀ j ∉ S, n j = 1 ∧ m j = 1 := fun j hj => by
    have hj' : lab j = .one := by simpa [hS] using hj
    obtain ⟨h1, h2⟩ := letter_one (lab j) hj' z
    simp only [n, m, h1, h2]
    norm_num
  have hin : ∀ j ∈ S, 6 ≤ n j ∧ m j ≤ n j - 4 := fun j hj => by
    have hj' : lab j ≠ .one := by simpa [hS] using hj
    obtain ⟨h6, h1, -⟩ := letter_bounds_two hz hz1 (lab j) hj'
    exact ⟨h6, by simp only [m, n]; omega⟩
  have hprodn : ∏ j, n j = ∏ j ∈ S, n j :=
    (Finset.prod_subset (Finset.subset_univ S) fun j _ hj => (hout j hj).1).symm
  have hprodm : ∏ j, m j = ∏ j ∈ S, m j :=
    (Finset.prod_subset (Finset.subset_univ S) fun j _ hj => (hout j hj).2).symm
  have hmle : ∏ j ∈ S, m j ≤ ∏ j ∈ S, (n j - 4) :=
    Finset.prod_le_prod fun j hj => (hin j hj).2
  obtain ⟨h1, -⟩ := prod_sub_four_add_le S n fun j hj => (hin j hj).1
  have h2 := sixteen_mul_add_le hs
  change (tRep F k lab z - 1).rank * 2 + ∏ j, m j = ∏ j, n j at h
  rw [hprodn, hprodm] at h
  omega

end Tensor

end CFSG.Quasithin.B45G2
