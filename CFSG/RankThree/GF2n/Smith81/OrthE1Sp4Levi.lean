module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFacts2

public section

open scoped Matrix
open CFSG.Open CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts

namespace Sp4TwistedLevi

variable {K : Type} [Field K]

@[expose] def uS (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 S 0 1

theorem uS_mul (S T : Matrix (Fin 2) (Fin 2) K) : uS S * uS T = uS (S + T) := by
  simp [uS, Matrix.fromBlocks_multiply, add_comm]

theorem uS_zero : uS (0 : Matrix (Fin 2) (Fin 2) K) = 1 := Matrix.fromBlocks_one

@[expose] def uGL (S : Matrix (Fin 2) (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨uS S, uS (-S), by rw [uS_mul, add_neg_cancel, uS_zero],
    by rw [uS_mul, neg_add_cancel, uS_zero]⟩

theorem uGL_mem {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) : uGL S ∈ StatedSp 2 K := by
  rw [StatedAPI.mem_statedSp_iff]
  change (uS S)ᵀ * _ * uS S = _
  simp [uS, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

@[expose] def uSp (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) : ↥(StatedSp 2 K) :=
  ⟨uGL S, uGL_mem hS⟩

@[expose] def Jm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem Jm_transpose : (Jm : Matrix (Fin 2) (Fin 2) K)ᵀ = Jm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm]

theorem smul_Jm_transpose (l : K) : (l • Jm : Matrix (Fin 2) (Fin 2) K)ᵀ = l • Jm := by
  rw [Matrix.transpose_smul, Jm_transpose]

theorem single_eq (c : K) :
    (Matrix.single 0 0 c : Matrix (Fin 2) (Fin 2) K) = !![c, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem det_isUnit {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) : IsUnit A.det := by
  rw [hA]; exact isUnit_one

theorem inv_mul_eq_one' {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (det_isUnit hA)

theorem mul_inv_eq_one' {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (det_isUnit hA)

theorem transpose_inv_mul' {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (A⁻¹)ᵀ * Aᵀ = 1 := by
  rw [← Matrix.transpose_mul, mul_inv_eq_one' hA, Matrix.transpose_one]

theorem transpose_mul_inv' {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    Aᵀ * (A⁻¹)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, inv_mul_eq_one' hA, Matrix.transpose_one]

theorem lev_mul_inv {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * Matrix.fromBlocks A⁻¹ 0 0 Aᵀ = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_inv_eq_one' hA, transpose_inv_mul' hA, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_one]

theorem inv_mul_lev {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    Matrix.fromBlocks A⁻¹ 0 0 Aᵀ * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [inv_mul_eq_one' hA, transpose_mul_inv' hA, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_one]

@[expose] noncomputable def levGL (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    GL (Fin 2 ⊕ Fin 2) K :=
  ⟨Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ, Matrix.fromBlocks A⁻¹ 0 0 Aᵀ, lev_mul_inv hA,
    inv_mul_lev hA⟩

theorem levGL_mem {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    levGL A hA ∈ StatedSp 2 K := by
  rw [StatedAPI.mem_statedSp_iff]
  change (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)ᵀ * _ * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ = _
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, inv_mul_eq_one' hA,
    transpose_mul_inv' hA]

@[expose] noncomputable def levSp (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    ↥(StatedSp 2 K) :=
  ⟨levGL A hA, levGL_mem hA⟩

theorem levSp_mem_levi {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    levSp A hA ∈ leviSL2 K :=
  Subgroup.subset_closure ⟨A, hA, rfl⟩

theorem levSp_val {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    ((levSp A hA : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
      Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ :=
  rfl

theorem levSp_inv_val {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (((levSp A hA)⁻¹ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
      Matrix.fromBlocks A⁻¹ 0 0 Aᵀ :=
  Units.inv_eq_of_mul_eq_one_right (lev_mul_inv hA)

theorem levGL_conj_uS {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1)
    (S : Matrix (Fin 2) (Fin 2) K) :
    Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * uS S * Matrix.fromBlocks A⁻¹ 0 0 Aᵀ =
      uS (A * S * Aᵀ) := by
  simp only [uS, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul, mul_inv_eq_one' hA, transpose_inv_mul' hA,
    Matrix.mul_assoc]

theorem lev_conj_block {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) (a b : K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ *
        Matrix.fromBlocks (b • (1 : Matrix (Fin 2) (Fin 2) K)) X 0 (a • 1) *
        Matrix.fromBlocks A⁻¹ 0 0 Aᵀ =
      Matrix.fromBlocks (b • (1 : Matrix (Fin 2) (Fin 2) K)) (A * X * Aᵀ) 0
        (a • (1 : Matrix (Fin 2) (Fin 2) K)) := by
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, mul_inv_eq_one' hA,
    transpose_inv_mul' hA, Matrix.mul_assoc, smul_zero, Matrix.mul_zero]

theorem diag_mul_inv {α β : K} (h : α * β = 1) :
    Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (β • 1) *
        Matrix.fromBlocks (β • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (α • 1) =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hb : β * α = 1 := (mul_comm β α).trans h
  simp [Matrix.fromBlocks_multiply, smul_smul, h, hb]

@[expose] def diagGL {α β : K} (h : α * β = 1) : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨Matrix.fromBlocks (α • 1) 0 0 (β • 1), Matrix.fromBlocks (β • 1) 0 0 (α • 1),
    diag_mul_inv h, diag_mul_inv ((mul_comm β α).trans h)⟩

theorem diagGL_mem {α β : K} (h : α * β = 1) : diagGL h ∈ StatedSp 2 K := by
  have hb : β * α = 1 := (mul_comm β α).trans h
  rw [StatedAPI.mem_statedSp_iff]
  change (Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (β • 1))ᵀ * _ *
    Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (β • 1) = _
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, smul_smul, h, hb]

@[expose] def diagSp {α β : K} (h : α * β = 1) : ↥(StatedSp 2 K) :=
  ⟨diagGL h, diagGL_mem h⟩

theorem diagSp_val {α β : K} (h : α * β = 1) :
    ((diagSp h : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
      Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (β • 1) :=
  rfl

theorem diagSp_inv_val {α β : K} (h : α * β = 1) :
    (((diagSp h)⁻¹ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
      Matrix.fromBlocks (β • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (α • 1) :=
  Units.inv_eq_of_mul_eq_one_right (diag_mul_inv h)

theorem diag_conj_block (a b : K) (s : Matrix (Fin 2) (Fin 2) K) :
    uS s * Matrix.fromBlocks (a • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (b • 1) * uS (-s) =
      Matrix.fromBlocks (a • (1 : Matrix (Fin 2) (Fin 2) K)) ((b - a) • s) 0
        (b • (1 : Matrix (Fin 2) (Fin 2) K)) := by
  simp only [uS, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_zero, sub_smul]
  refine Matrix.fromBlocks_inj.2 ⟨rfl, ?_, rfl, ?_⟩
  · abel
  · simp

theorem levSp_comm_diag {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) {α β : K}
    (h : α * β = 1) : levSp A hA * diagSp h = diagSp h * levSp A hA := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  show Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * Matrix.fromBlocks (α • 1) 0 0 (β • 1) =
    Matrix.fromBlocks (α • 1) 0 0 (β • 1) * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_zero]

theorem levSp_comm_uS {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1)
    {T : Matrix (Fin 2) (Fin 2) K} (hT : Tᵀ = T) (hc : A * T = T * (A⁻¹)ᵀ) :
    levSp A hA * uSp T hT = uSp T hT * levSp A hA := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  show Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ * uS T = uS T * Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ
  simp only [uS, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul]
  rw [hc]

theorem jm_comm [CharP K 2] {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    B * Jm = Jm * (B⁻¹)ᵀ := by
  have hN : !![B 1 1, -B 0 1; -B 1 0, B 0 0] * B = 1 := by
    rw [Matrix.det_fin_two] at hB
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB
  have hinv : B⁻¹ = !![B 1 1, -B 0 1; -B 1 0, B 0 0] := Matrix.inv_eq_left_inv hN
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem mem_centralizer_of_levi {u : ↥(StatedSp 2 K)}
    (h : ∀ (B : Matrix (Fin 2) (Fin 2) K) (hB : B.det = 1), levSp B hB * u = u * levSp B hB) :
    u ∈ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) := by
  have hle : leviSL2 K ≤ Subgroup.centralizer ({u} : Set ↥(StatedSp 2 K)) := by
    rw [leviSL2, Subgroup.closure_le]
    rintro g ⟨B, hB, hg⟩
    have hgB : g = levSp B hB := by
      apply Subtype.ext
      apply Units.ext
      exact hg
    rw [SetLike.mem_coe, hgB, Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    exact (h B hB).symm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (hle hk) u (Set.mem_singleton u)).symm

@[expose] def Good (H : Subgroup ↥(StatedSp 2 K)) (S : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ h ∈ H, ((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = uS S

theorem Good.add {H : Subgroup ↥(StatedSp 2 K)} {S T : Matrix (Fin 2) (Fin 2) K}
    (hS : Good H S) (hT : Good H T) : Good H (S + T) := by
  obtain ⟨h, hh, hm⟩ := hS
  obtain ⟨k, hk, hk'⟩ := hT
  refine ⟨h * k, H.mul_mem hh hk, ?_⟩
  rw [Subgroup.coe_mul, Units.val_mul, hm, hk', uS_mul]

theorem Good.conj {H : Subgroup ↥(StatedSp 2 K)} (hL : leviSL2 K ≤ H)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) {S : Matrix (Fin 2) (Fin 2) K}
    (hS : Good H S) : Good H (A * S * Aᵀ) := by
  obtain ⟨h, hh, hm⟩ := hS
  have hl : levSp A hA ∈ H := hL (levSp_mem_levi hA)
  refine ⟨levSp A hA * h * (levSp A hA)⁻¹, H.mul_mem (H.mul_mem hl hh) (H.inv_mem hl), ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hm]
  exact levGL_conj_uS hA S

theorem exists_sq_eq [Finite K] [CharP K 2] (ν t : K) (hν : ν ≠ 0) :
    ∃ w : K, ν * w ^ 2 = t := by
  have hinj : Function.Injective (fun w : K => w ^ 2) := by
    intro a b hab
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hab with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj (t / ν)
  refine ⟨w, ?_⟩
  simp only at hw
  rw [hw]
  field_simp

theorem exists_ne_zero_one [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ α : K, α ≠ 0 ∧ α ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ α : K, α ≠ 0 → α = 1 := fun α h0 => by
    by_contra h1
    exact hcon ⟨α, h0, h1⟩
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro a
    by_cases ha : a = 0
    · exact ⟨false, by simp [ha]⟩
    · exact ⟨true, by simp [hcon' a ha]⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  simp at this
  omega

theorem block_prod {α β : K} (h : α * β = 1) (s T : Matrix (Fin 2) (Fin 2) K) :
    Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) ((β - α) • s) 0 (β • 1) *
        Matrix.fromBlocks (β • (1 : Matrix (Fin 2) (Fin 2) K)) ((α - β) • T) 0 (α • 1) =
      uS ((α ^ 2 - 1) • (T - s)) := by
  have e1 : (α - β) * α = α ^ 2 - 1 := by linear_combination (-1 : K) * h
  have e2 : α * (β - α) = -(α ^ 2 - 1) := by linear_combination h
  have hb : β * α = 1 := (mul_comm β α).trans h
  simp only [uS, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    smul_zero, h, hb, one_smul]
  rw [e1, e2, smul_sub, neg_smul, ← sub_eq_add_neg]

theorem comm_mat {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1)
    (s : Matrix (Fin 2) (Fin 2) K) {α β : K} (h : α * β = 1) :
    (uS s * Matrix.fromBlocks (α • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (β • 1) * uS (-s)) *
      (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ *
        (uS s * Matrix.fromBlocks (β • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (α • 1) * uS (-s)) *
        Matrix.fromBlocks A⁻¹ 0 0 Aᵀ) =
      uS ((α ^ 2 - 1) • (A * s * Aᵀ - s)) := by
  rw [diag_conj_block α β s, diag_conj_block β α s, lev_conj_block hA α β ((α - β) • s),
    Matrix.mul_smul, Matrix.smul_mul, block_prod h s (A * s * Aᵀ)]

@[expose] def hgrp (x : ↥(StatedSp 2 K)) : Subgroup ↥(StatedSp 2 K) :=
  leviSL2 K ⊔
    (Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K))).map (MulAut.conj x).toMonoidHom

end Sp4TwistedLevi

open Sp4TwistedLevi

theorem sp4TwistedLevi_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ∀ (c : K) (x : ↥(StatedSp 2 K)), c ≠ 0 →
        ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          Matrix.fromBlocks 1 (Matrix.single 0 0 c) 0 1 →
        siegelRadical K ≤ leviSL2 K ⊔
          (Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K))).map (MulAut.conj x).toMonoidHom := by
  intro K _ _ _ hK c x hc hx
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [single_eq] at hx
  have hL : leviSL2 K ≤ hgrp x := fun g hg => Subgroup.mem_sup_left hg
  have hC : ∀ g ∈ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)),
      MulAut.conj x g ∈ hgrp x := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hg)
  have hxi : (((x : GL (Fin 2 ⊕ Fin 2) K))⁻¹ : GL (Fin 2 ⊕ Fin 2) K).val =
      uS (-!![c, 0; 0, 0]) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hx, uS, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, neg_add_cancel, Matrix.fromBlocks_one]
  have hconj : ∀ g : ↥(StatedSp 2 K),
      ((MulAut.conj x g : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
        uS !![c, 0; 0, 0] * ((g : GL (Fin 2 ⊕ Fin 2) K)).val * uS (-!![c, 0; 0, 0]) := by
    intro g
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul, Units.val_mul, hxi, hx]
    rfl
  obtain ⟨α, hα0, hα1⟩ := exists_ne_zero_one hK
  obtain ⟨β, hαβ⟩ : ∃ β : K, α * β = 1 := ⟨α⁻¹, mul_inv_cancel₀ hα0⟩
  have h1α : α ^ 2 - 1 ≠ 0 := by
    intro h
    have e : (α - 1) * (α - 1) = 0 := by linear_combination h + (1 - α) * h2
    exact hα1 (sub_eq_zero.1 (mul_self_eq_zero.1 e))
  have hν0 : (α ^ 2 - 1) * c ≠ 0 := mul_ne_zero h1α hc
  have hcD : diagSp hαβ ∈ Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) :=
    mem_centralizer_of_levi (fun B hB => levSp_comm_diag hB hαβ)
  have hcJ : ∀ l : K, uSp (l • Jm) (smul_Jm_transpose l) ∈
      Subgroup.centralizer (leviSL2 K : Set ↥(StatedSp 2 K)) := fun l =>
    mem_centralizer_of_levi (fun B hB => levSp_comm_uS hB (smul_Jm_transpose l)
      (by rw [Matrix.mul_smul, jm_comm hB, Matrix.smul_mul]))
  have hGJ : ∀ l : K, Good (hgrp x) (l • Jm) := by
    intro l
    refine ⟨MulAut.conj x (uSp (l • Jm) (smul_Jm_transpose l)), hC _ (hcJ l), ?_⟩
    rw [hconj]
    show uS !![c, 0; 0, 0] * uS (l • Jm) * uS (-!![c, 0; 0, 0]) = uS (l • Jm)
    rw [uS_mul, uS_mul]
    congr 1
    abel
  have hGE22 : ∀ t : K, Good (hgrp x) !![0, 0; 0, t] := by
    intro t
    obtain ⟨w, hw⟩ := exists_sq_eq ((α ^ 2 - 1) * c) t hν0
    have hAw : (!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two]
    have hf : levSp _ hAw ∈ hgrp x := hL (levSp_mem_levi hAw)
    have hyy : MulAut.conj x (diagSp hαβ) ∈ hgrp x := hC _ hcD
    have hyy' : MulAut.conj x ((diagSp hαβ)⁻¹) ∈ hgrp x := hC _ (Subgroup.inv_mem _ hcD)
    have hg1 : MulAut.conj x (diagSp hαβ) *
        (levSp _ hAw * MulAut.conj x ((diagSp hαβ)⁻¹) * (levSp _ hAw)⁻¹) ∈ hgrp x :=
      Subgroup.mul_mem _ hyy (Subgroup.mul_mem _ (Subgroup.mul_mem _ hf hyy')
        (Subgroup.inv_mem _ hf))
    have hmat : ((MulAut.conj x (diagSp hαβ) *
        (levSp _ hAw * MulAut.conj x ((diagSp hαβ)⁻¹) * (levSp _ hAw)⁻¹) :
          ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K).val =
        uS (((α ^ 2 - 1) * c) • !![0, w; w, w ^ 2]) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hconj, hconj, diagSp_val, diagSp_inv_val, levSp_val, levSp_inv_val]
      have hT : (!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, w; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have e1 : (α ^ 2 - 1) • ((!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) K) *
          !![c, 0; 0, 0] * (!![1, 0; w, 1])ᵀ - !![c, 0; 0, 0]) =
          ((α ^ 2 - 1) * c) • (!![0, w; w, w ^ 2] : Matrix (Fin 2) (Fin 2) K) := by
        rw [hT]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two] <;> ring
      exact (comm_mat hAw (!![c, 0; 0, 0]) hαβ).trans (congrArg uS e1)
    have hgE : Good (hgrp x) (((α ^ 2 - 1) * c) • !![0, w; w, w ^ 2]) := ⟨_, hg1, hmat⟩
    have hsum := Good.add hgE (hGJ (((α ^ 2 - 1) * c) * w))
    have e2 : ((α ^ 2 - 1) * c) • (!![0, w; w, w ^ 2] : Matrix (Fin 2) (Fin 2) K) +
        (((α ^ 2 - 1) * c) * w) • Jm = (!![0, 0; 0, t] : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hw]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Jm] <;>
        first | ring1 | linear_combination ((α ^ 2 - 1) * c * w) * h2
    rw [e2] at hsum
    exact hsum
  have hAJ : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  have hGE11 : ∀ t : K, Good (hgrp x) !![t, 0; 0, 0] := by
    intro t
    have key := Good.conj hL hAJ (hGE22 t)
    have hT : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, -1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e : !![0, 1; -1, 0] * !![0, 0; 0, t] * (!![0, 1; -1, 0])ᵀ =
        (!![t, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) := by
      rw [hT]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
    rw [e] at key
    exact key
  have hAu : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  have hGM3 : ∀ t : K, Good (hgrp x) !![t, t; t, t] := by
    intro t
    have key := Good.conj hL hAu (hGE22 t)
    have hT : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, 0; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e : !![1, 1; 0, 1] * !![0, 0; 0, t] * (!![1, 1; 0, 1])ᵀ =
        (!![t, t; t, t] : Matrix (Fin 2) (Fin 2) K) := by
      rw [hT]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
    rw [e] at key
    exact key
  have hGsym : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → Good (hgrp x) S := by
    intro S hS
    have hs : S 0 1 = S 1 0 := by
      simpa [Matrix.transpose_apply] using congrFun (congrFun hS 1) 0
    have e : S = (!![S 0 0 + S 0 1, 0; 0, 0] + !![0, 0; 0, S 1 1 + S 0 1]) +
        !![S 0 1, S 0 1; S 0 1, S 0 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← hs] <;>
        first | ring1 | linear_combination (-S 0 1) * h2 | linear_combination (S 0 1) * h2
    rw [e]
    exact Good.add (Good.add (hGE11 _) (hGE22 _)) (hGM3 _)
  show siegelRadical K ≤ hgrp x
  rw [siegelRadical, Subgroup.closure_le]
  rintro g ⟨S, hS, hg⟩
  obtain ⟨h, hh, hm⟩ := hGsym S hS
  have hgh : g = h := Subtype.ext (Units.ext (hg.trans hm.symm))
  rw [hgh]
  exact hh

end CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts

end
