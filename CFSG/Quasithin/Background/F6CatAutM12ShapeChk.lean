module

public import CFSG.Quasithin.Recognition.M12AmalAutJCheck

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge

@[expose] def shNIdx : List ℕ :=
  [0, 22, 106, 84, 20, 28, 65, 40, 36, 70, 111, 125, 26, 123, 67, 120]

@[expose] def shZ4Idx (g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : ℕ :=
  ([[0, 22, 106, 84], [20, 28, 65, 40], [36, 70, 111, 125], [26, 123, 67, 120]].getD
    g.1.toAdd.val []).getD g.2.toAdd.val 0

theorem sh_z4_mul_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    telMul (shZ4Idx g) (shZ4Idx h) = shZ4Idx (g * h) := by decide +kernel

theorem sh_z4_inj_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    shZ4Idx g = shZ4Idx h → g = h := by decide +kernel

theorem sh_z4_one_chk : shZ4Idx 1 = 0 := by decide +kernel

theorem sh_z4_mem_chk : ∀ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    shZ4Idx g ∈ shNIdx := by decide +kernel

theorem sh_z4_surj_chk : ∀ i ∈ shNIdx, ∃ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    shZ4Idx g = i := by decide +kernel

theorem sh_N_lt_chk : ∀ i ∈ shNIdx, i < 128 := by decide +kernel

theorem sh_N_norm_chk : NormOK shNIdx := by decide +kernel

@[expose] def shPowIdx (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => telMul (shPowIdx i m) i

theorem sh_sigma_sq_chk : telMul 1 1 ∈ shNIdx := by decide +kernel

theorem sh_sigma_rho_chk : telMul (telMul (telMul 1 2) (telInv 1)) 2 ∈ shNIdx := by
  decide +kernel

theorem sh_rho_four_chk : shPowIdx 2 4 ∈ shNIdx := by decide +kernel

theorem sh_rho_two_chk : shPowIdx 2 2 ∉ shNIdx := by decide +kernel

theorem sh_sigma_not_chk : ∀ m < 4, ∀ k ∈ shNIdx, telMul (shPowIdx 2 m) k ≠ 1 := by
  decide +kernel

@[expose] def shRIdx : List ℕ :=
  [0, 1, 3, 5, 7, 9, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 45, 47, 48,
    50, 52, 56, 58, 59, 60, 62, 65, 67, 68, 70, 72, 76, 78, 79, 81, 83, 84, 86, 89, 90, 91, 95, 97,
    101, 103, 104, 106, 109, 110, 111, 115, 117, 120, 121, 123, 124, 125, 127]

theorem sh_R_chk : 0 ∈ shRIdx ∧ (∀ i ∈ shRIdx, i < 128) ∧
    (∀ i ∈ shRIdx, ∀ j ∈ shRIdx, telMul i j ∈ shRIdx) ∧ (∀ i ∈ shRIdx, telInv i ∈ shRIdx) := by
  decide +kernel

theorem sh_R_norm_chk : NormOK shRIdx := by decide +kernel

@[expose] def shVWIdx (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : ℕ :=
  ([[0, 3], [1, 5]].getD g.1.toAdd.val []).getD g.2.toAdd.val 0

theorem sh_VW_chk : ∀ g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
    shVWIdx g ∈ shRIdx := by decide +kernel

@[expose] def shYPowL : ℕ → List ℕ
  | 0 => idl
  | m + 1 => compL (shYPowL m) (gl 4)

theorem sh_y_cube_chk : shYPowL 3 = idl := by decide +kernel

@[expose] def shChiL
    (g : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    List ℕ :=
  compL (shYPowL g.1.toAdd.val) (tl (shVWIdx g.2))

theorem sh_chi_one_chk : shChiL 1 = idl := by decide +kernel

theorem sh_chi_mul_chk :
    ∀ g h : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
      ∃ k ∈ shNIdx, compL (shChiL (g * h)) (tl k) = compL (shChiL g) (shChiL h) := by
  decide +kernel

theorem sh_chi_inj_chk :
    ∀ g : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
      (∃ k ∈ shNIdx, shChiL g = tl k) → g = 1 := by decide +kernel

end CFSG.Quasithin.M12AmalAut
