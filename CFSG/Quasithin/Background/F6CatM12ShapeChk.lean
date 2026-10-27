module

public import CFSG.Quasithin.Recognition.M12AmalCheck2

public section

namespace CFSG.Quasithin.M12Amal

open CFSG.Sporadic.Bridge

@[expose] def NIdx : List ℕ := [0, 15, 29, 55, 2, 32, 49, 63, 8, 52, 4, 46, 22, 62, 13, 60]

@[expose] def z4Idx (g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : ℕ :=
  ([[0, 15, 29, 55], [2, 32, 49, 63], [8, 52, 4, 46], [22, 62, 13, 60]].getD
    g.1.toAdd.val []).getD g.2.toAdd.val 0

theorem z4_mul_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    compL (tl (z4Idx g)) (tl (z4Idx h)) = tl (z4Idx (g * h)) := by decide +kernel

theorem z4_inj_chk : ∀ g h : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    z4Idx g = z4Idx h → g = h := by decide +kernel

theorem z4_one_chk : z4Idx 1 = 0 := by decide +kernel

theorem z4_mem_chk : ∀ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), z4Idx g ∈ NIdx := by
  decide +kernel

theorem z4_surj_chk : ∀ i ∈ NIdx, ∃ g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    z4Idx g = i := by decide +kernel

theorem N_lt_chk : ∀ i ∈ NIdx, i < 64 := by decide +kernel

theorem N_norm_chk : ∀ g ∈ [0, 1, 2, 4], ∀ i ∈ NIdx,
    (∃ k ∈ NIdx, compL (compL (gl g) (tl i)) (gil g) = tl k) ∧
      (∃ k ∈ NIdx, compL (compL (gil g) (tl i)) (gl g) = tl k) := by decide +kernel

theorem T_sq_chk : ∀ i < 64, ∃ k ∈ NIdx, compL (tl i) (tl i) = tl k := by decide +kernel

@[expose] def rhoL : List ℕ := compL (gl 4) (gl 2)

@[expose] def rhoPowL : ℕ → List ℕ
  | 0 => idl
  | m + 1 => compL (rhoPowL m) rhoL

theorem sigma_sq_chk : ∃ k ∈ NIdx, compL (gl 0) (gl 0) = tl k := by decide +kernel

theorem sigma_rho_chk : ∃ k ∈ NIdx,
    compL (compL (compL (gl 0) rhoL) (gil 0)) rhoL = tl k := by decide +kernel

theorem rho_six_chk : ∃ k ∈ NIdx, rhoPowL 6 = tl k := by decide +kernel

theorem rho_two_chk : ∀ k ∈ NIdx, rhoPowL 2 ≠ tl k := by decide +kernel

theorem rho_three_chk : ∀ k ∈ NIdx, rhoPowL 3 ≠ tl k := by decide +kernel

theorem sigma_not_chk : ∀ m < 6, ∀ k ∈ NIdx, compL (rhoPowL m) (tl k) ≠ gl 0 := by
  decide +kernel

end CFSG.Quasithin.M12Amal
