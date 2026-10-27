module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def upMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of ![![1, c₀, c₁, c₂, c₃, c₄],
    ![0, 1, c₅, c₆, c₇, c₃ + c₇ * c₀ + (c₆ + c₈ * c₅) * (c₁ + c₅ * c₀) +
        c₅ * (c₂ + c₆ * c₀ + c₈ * (c₁ + c₅ * c₀))],
    ![0, 0, 1, c₈, c₆ + c₈ * c₅, c₂ + c₆ * c₀ + c₈ * (c₁ + c₅ * c₀)],
    ![0, 0, 0, 1, c₅, c₁ + c₅ * c₀],
    ![0, 0, 0, 0, 1, c₀],
    ![0, 0, 0, 0, 0, 1]]

@[expose] def loMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈)ᵀ

@[expose] def bits6 (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) : ℕ :=
  (if b₀ then 1 else 0) + (if b₁ then 2 else 0) + (if b₂ then 4 else 0) +
    (if b₃ then 8 else 0) + (if b₄ then 16 else 0) + (if b₅ then 32 else 0)

@[expose] def upB (n : ℕ) : BM :=
  let c₀ := n.testBit 0
  let c₁ := n.testBit 1
  let c₂ := n.testBit 2
  let c₃ := n.testBit 3
  let c₄ := n.testBit 4
  let c₅ := n.testBit 5
  let c₆ := n.testBit 6
  let c₇ := n.testBit 7
  let c₈ := n.testBit 8
  let e35 := c₁ ^^ (c₅ && c₀)
  let e24 := c₆ ^^ (c₈ && c₅)
  let e25 := c₂ ^^ (c₆ && c₀) ^^ (c₈ && e35)
  let e15 := c₃ ^^ (c₇ && c₀) ^^ (e24 && e35) ^^ (c₅ && e25)
  ![bits6 true c₀ c₁ c₂ c₃ c₄, bits6 false true c₅ c₆ c₇ e15, bits6 false false true c₈ e24 e25,
    bits6 false false false true c₅ e35, bits6 false false false false true c₀,
    bits6 false false false false false true]

@[expose] def loB (n : ℕ) : BM := btrans (upB n)

theorem upMat_eq_toMat_upB : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ZMod 2,
    upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ = toMat (upB (c₀.val + 2 * c₁.val + 4 * c₂.val +
      8 * c₃.val + 16 * c₄.val + 32 * c₅.val + 64 * c₆.val + 128 * c₇.val + 256 * c₈.val)) := by
  decide +kernel

theorem loMat_eq_toMat_loB (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ZMod 2) :
    loMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ = toMat (loB (c₀.val + 2 * c₁.val + 4 * c₂.val +
      8 * c₃.val + 16 * c₄.val + 32 * c₅.val + 64 * c₆.val + 128 * c₇.val + 256 * c₈.val)) := by
  rw [loMat, upMat_eq_toMat_upB, loB, toMat_btrans]

theorem qs_conj_y_bits : ∀ s : Fin 3, ∀ n < 512, IsQs s (toMat (upB n)) →
    IsQs s (toMat (bmul (bmul (yB s) (upB n)) (yB s))) := by
  decide +kernel

theorem qm_conj_x_bits : ∀ s : Fin 3, ∀ n < 512, IsQm s (toMat (loB n)) →
    IsQm s (toMat (bmul (bmul (xB s) (loB n)) (xB s))) := by
  decide +kernel

theorem pow_eight_bits : ∀ n < 512,
    bmul (bmul (bmul (upB n) (upB n)) (bmul (upB n) (upB n)))
        (bmul (bmul (upB n) (upB n)) (bmul (upB n) (upB n))) = bone ∧
      bmul (bmul (bmul (loB n) (loB n)) (bmul (loB n) (loB n)))
        (bmul (bmul (loB n) (loB n)) (bmul (loB n) (loB n))) = bone := by
  decide +kernel

theorem gramJ_mul_self : gramJ * gramJ = 1 := by decide +kernel

theorem symp_transpose {M : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : Mᵀ * gramJ * M = gramJ) : M * gramJ * Mᵀ = gramJ := by
  have h1 : (gramJ * Mᵀ * gramJ) * M = 1 := by
    calc (gramJ * Mᵀ * gramJ) * M = gramJ * (Mᵀ * gramJ * M) := by simp only [Matrix.mul_assoc]
      _ = gramJ * gramJ := by rw [h]
      _ = 1 := gramJ_mul_self
  have h2 : M * (gramJ * Mᵀ * gramJ) = 1 := mul_eq_one_comm.mp h1
  calc M * gramJ * Mᵀ = (M * (gramJ * Mᵀ * gramJ)) * gramJ := by
        simp only [Matrix.mul_assoc, gramJ_mul_self, Matrix.mul_one]
    _ = gramJ := by rw [h2, Matrix.one_mul]

theorem symp_apply (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (i j : Fin 6) :
    (Mᵀ * gramJ * M) i j = M 0 i * M 5 j + M 1 i * M 4 j + M 2 i * M 3 j + M 3 i * M 2 j +
      M 4 i * M 1 j + M 5 i * M 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_six, gramJ, gramB, toMat, Nat.testBit]
  ring

theorem eq_upMat {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hU : IsUpU M)
    (hS : Mᵀ * gramJ * M = gramJ) :
    M = upMat (M 0 1) (M 0 2) (M 0 3) (M 0 4) (M 0 5) (M 1 2) (M 1 3) (M 1 4) (M 2 3) := by
  have d0 : M 0 0 = 1 := (hU 0 0).2 rfl
  have d1 : M 1 1 = 1 := (hU 1 1).2 rfl
  have d2 : M 2 2 = 1 := (hU 2 2).2 rfl
  have d3 : M 3 3 = 1 := (hU 3 3).2 rfl
  have d4 : M 4 4 = 1 := (hU 4 4).2 rfl
  have d5 : M 5 5 = 1 := (hU 5 5).2 rfl
  have z10 : M 1 0 = 0 := (hU 1 0).1 (by decide)
  have z20 : M 2 0 = 0 := (hU 2 0).1 (by decide)
  have z30 : M 3 0 = 0 := (hU 3 0).1 (by decide)
  have z40 : M 4 0 = 0 := (hU 4 0).1 (by decide)
  have z50 : M 5 0 = 0 := (hU 5 0).1 (by decide)
  have z21 : M 2 1 = 0 := (hU 2 1).1 (by decide)
  have z31 : M 3 1 = 0 := (hU 3 1).1 (by decide)
  have z41 : M 4 1 = 0 := (hU 4 1).1 (by decide)
  have z51 : M 5 1 = 0 := (hU 5 1).1 (by decide)
  have z32 : M 3 2 = 0 := (hU 3 2).1 (by decide)
  have z42 : M 4 2 = 0 := (hU 4 2).1 (by decide)
  have z52 : M 5 2 = 0 := (hU 5 2).1 (by decide)
  have z43 : M 4 3 = 0 := (hU 4 3).1 (by decide)
  have z53 : M 5 3 = 0 := (hU 5 3).1 (by decide)
  have z54 : M 5 4 = 0 := (hU 5 4).1 (by decide)
  have e15 := congrFun (congrFun hS 1) 5
  have e24 := congrFun (congrFun hS 2) 4
  have e25 := congrFun (congrFun hS 2) 5
  have e34 := congrFun (congrFun hS 3) 4
  have e35 := congrFun (congrFun hS 3) 5
  have e45 := congrFun (congrFun hS 4) 5
  rw [symp_apply] at e15 e24 e25 e34 e35 e45
  have g15 : gramJ 1 5 = 0 := by decide
  have g24 : gramJ 2 4 = 0 := by decide
  have g25 : gramJ 2 5 = 0 := by decide
  have g34 : gramJ 3 4 = 0 := by decide
  have g35 : gramJ 3 5 = 0 := by decide
  have g45 : gramJ 4 5 = 0 := by decide
  rw [g15] at e15
  rw [g24] at e24
  rw [g25] at e25
  rw [g34] at e34
  rw [g35] at e35
  rw [g45] at e45
  simp only [d0, d1, d2, d3, d4, d5, z10, z20, z30, z40, z50, z21, z31, z41, z51, z32, z42, z52,
    z43, z53, z54, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add] at e15 e24 e25
  simp only [d0, d1, d2, d3, d4, d5, z10, z20, z30, z40, z50, z21, z31, z41, z51, z32, z42, z52,
    z43, z53, z54, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add] at e34 e35 e45
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have h45 : M 4 5 = M 0 1 := key _ _ e15
  have h34 : M 3 4 = M 1 2 := key _ _ e24
  rw [h45] at e25 e35 e45
  rw [h34] at e34 e45
  have h35 : M 3 5 = M 0 2 + M 1 2 * M 0 1 := key _ _ e25
  have h24 : M 2 4 = M 1 3 + M 2 3 * M 1 2 := key _ _ e34
  rw [h35] at e35 e45
  have h25 : M 2 5 = M 0 3 + M 1 3 * M 0 1 + M 2 3 * (M 0 2 + M 1 2 * M 0 1) := key _ _ e35
  rw [h24, h25] at e45
  have h15 := key _ _ e45
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [upMat, d0, d1, d2, d3, d4, d5, z10, z20, z30, z40, z50, z21, z31, z41, z51, z32, z42,
      z52, z43, z53, z54, h45, h34, h35, h24, h25, h15]

theorem eq_loMat {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hL : IsLoU M)
    (hS : Mᵀ * gramJ * M = gramJ) :
    M = loMat (M 1 0) (M 2 0) (M 3 0) (M 4 0) (M 5 0) (M 2 1) (M 3 1) (M 4 1) (M 3 2) := by
  have hU : IsUpU Mᵀ := fun a b => ⟨fun hba => (hL b a).1 hba, fun hab => (hL b a).2 hab.symm⟩
  have hS' : Mᵀᵀ * gramJ * Mᵀ = gramJ := by
    rw [transpose_transpose]
    exact symp_transpose hS
  have h1 := eq_upMat hU hS'
  have h3 : M = (upMat (Mᵀ 0 1) (Mᵀ 0 2) (Mᵀ 0 3) (Mᵀ 0 4) (Mᵀ 0 5) (Mᵀ 1 2) (Mᵀ 1 3) (Mᵀ 1 4)
      (Mᵀ 2 3))ᵀ := by
    conv_lhs => rw [← transpose_transpose M, h1]
  exact h3

theorem exists_upB {g : G6} (h : IsUpU (gM g)) : ∃ n < 512, gM g = toMat (upB n) := by
  have h' := eq_upMat h (gM_symp g)
  rw [upMat_eq_toMat_upB] at h'
  refine ⟨_, ?_, h'⟩
  have e0 := ZMod.val_lt (gM g 0 1)
  have e1 := ZMod.val_lt (gM g 0 2)
  have e2 := ZMod.val_lt (gM g 0 3)
  have e3 := ZMod.val_lt (gM g 0 4)
  have e4 := ZMod.val_lt (gM g 0 5)
  have e5 := ZMod.val_lt (gM g 1 2)
  have e6 := ZMod.val_lt (gM g 1 3)
  have e7 := ZMod.val_lt (gM g 1 4)
  have e8 := ZMod.val_lt (gM g 2 3)
  omega

theorem exists_loB {g : G6} (h : IsLoU (gM g)) : ∃ n < 512, gM g = toMat (loB n) := by
  have h' := eq_loMat h (gM_symp g)
  rw [loMat_eq_toMat_loB] at h'
  refine ⟨_, ?_, h'⟩
  have e0 := ZMod.val_lt (gM g 1 0)
  have e1 := ZMod.val_lt (gM g 2 0)
  have e2 := ZMod.val_lt (gM g 3 0)
  have e3 := ZMod.val_lt (gM g 4 0)
  have e4 := ZMod.val_lt (gM g 5 0)
  have e5 := ZMod.val_lt (gM g 2 1)
  have e6 := ZMod.val_lt (gM g 3 1)
  have e7 := ZMod.val_lt (gM g 4 1)
  have e8 := ZMod.val_lt (gM g 3 2)
  omega

theorem Qs_conj_y {s : Fin 3} {q : G6} (h : IsQs s (gM q)) : IsQs s (gM (yE s * q * yE s)) := by
  obtain ⟨n, hn, hq⟩ := exists_upB h.1
  have h1 := qs_conj_y_bits s n hn (hq ▸ h)
  change IsQs s (yM s * gM q * yM s)
  rw [hq, yM_eq_toMat, ← toMat_bmul, ← toMat_bmul]
  exact h1

theorem Qm_conj_x {s : Fin 3} {q : G6} (h : IsQm s (gM q)) : IsQm s (gM (xE s * q * xE s)) := by
  obtain ⟨n, hn, hq⟩ := exists_loB h.1
  have h1 := qm_conj_x_bits s n hn (hq ▸ h)
  change IsQm s (xM s * gM q * xM s)
  rw [hq, xM_eq_toMat, ← toMat_bmul, ← toMat_bmul]
  exact h1

theorem pow_eight_matrix (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    A ^ 8 = ((A * A) * (A * A)) * ((A * A) * (A * A)) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem gM_pow_eight (u : G6) : gM (u ^ 8) = gM u ^ 8 := by
  simp [gM, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem Ugrp_pow_eight : ∀ u ∈ Ugrp, u ^ 8 = 1 := by
  intro u hu
  obtain ⟨n, hn, hq⟩ := exists_upB (mem_Ugrp.mp hu)
  apply gM_injective
  rw [gM_pow_eight, pow_eight_matrix, hq, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul,
    (pow_eight_bits n hn).1, toMat_bone]
  rfl

theorem Lgrp_pow_eight : ∀ u ∈ Lgrp, u ^ 8 = 1 := by
  intro u hu
  obtain ⟨n, hn, hq⟩ := exists_loB (mem_Lgrp.mp hu)
  apply gM_injective
  rw [gM_pow_eight, pow_eight_matrix, hq, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul,
    (pow_eight_bits n hn).2, toMat_bone]
  rfl

theorem isPGroup_Ugrp : IsPGroup 2 ↥Ugrp := fun u => ⟨3, Subtype.ext (Ugrp_pow_eight u u.2)⟩

theorem isPGroup_Lgrp : IsPGroup 2 ↥Lgrp := fun u => ⟨3, Subtype.ext (Lgrp_pow_eight u u.2)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
