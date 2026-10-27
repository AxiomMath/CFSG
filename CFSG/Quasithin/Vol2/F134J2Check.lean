module

public import CFSG.Quasithin.Vol2.F134J2Tables

public section

namespace CFSG.Quasithin.F134

open CFSG.Sporadic.Bridge.J2

theorem j2_code_a : glCode uA = j2aC := by
  change matCode14 (toM mA) = j2aC
  decide +kernel

theorem j2_code_b : glCode uB = j2bC := by
  change matCode14 (toM mB) = j2bC
  decide +kernel

theorem j2_code_one : glCode (1 : GL (Fin 14) (ZMod 5)) = j2oneC := by
  change matCode14 (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) = j2oneC
  decide +kernel

theorem j2_tel_zero : j2Tel 0 = j2oneC := by decide +kernel

theorem j2_dw_zero : j2DW.getD 0 [] = [] := by decide +kernel

theorem j2_tgen_check : ∀ k < 3, j2WordC (j2TGenW.getD k []) = j2TG k := by decide +kernel

theorem j2_nxt_check : ∀ i < 128, ∀ k < 3, j2Nxt (3 * i + k) < 128 ∧
    mul14 (j2Tel i) (j2TG k) = j2Tel (j2Nxt (3 * i + k)) := by
  decide +kernel

theorem j2_par_check : ∀ i < 128, 0 < i → j2Par i / 4 < i ∧ j2Par i % 4 < 3 ∧
    mul14 (j2Tel (j2Par i / 4)) (j2TG (j2Par i % 4)) = j2Tel i := by
  decide +kernel

theorem j2_tel_ne : ∀ i < 128, ∀ j < i, j2Tel i ≠ j2Tel j := by decide +kernel

theorem j2_d_check : ∀ j < 72, j2WordC (j2DW.getD j []) = j2D j := by decide +kernel

@[expose] def j2AWC : List ℕ → ℕ
  | [] => j2oneC
  | c :: w => mul14 (if c = 3 then j2bC else j2TG c) (j2AWC w)

theorem j2_a_check : j2AWC j2AW = j2aC ∧ ∀ c ∈ j2AW, c < 4 := by decide +kernel

theorem j2_bad_check : ∀ j < 72, 6 ≤ j →
    (j2Bad j % 16 = 5 ∨ j2Bad j % 16 = 7) ∧ j2Bad j / 256 < 128 ∧
      powC14 j2oneC (j2Bad j % 16)
          (powC14 j2oneC (j2Bad j / 16 % 16) (mul14 (j2D j) (j2Tel (j2Bad j / 256)))) =
        j2oneC ∧
      powC14 j2oneC (j2Bad j / 16 % 16) (mul14 (j2D j) (j2Tel (j2Bad j / 256))) ≠ j2oneC := by
  decide +kernel

theorem j2_cos_check : ∀ j < 6, ∀ i < 128, j2Cos j i / 128 < (if j < 3 then 1 else 2) ∧
    mul14 (j2Tel i) (j2D j) =
    mul14 (mul14 (j2Tel (if j2Cos j i / 128 = 0 then 0 else 3)) (j2D j))
      (j2Tel (j2Cos j i % 128)) := by
  decide +kernel

@[expose] def j2CC (s : ℕ) : ℕ :=
  mul14 (j2Tel (if s = 4 ∨ s = 6 ∨ s = 8 then 3 else 0))
    (j2D (if s ≤ 3 then s else (s + 3) / 2))

@[expose] def j2X1 : ℕ := mul14 (j2D 1) (j2Tel 3)

@[expose] def j2X2 : ℕ := mul14 (j2D 3) (j2Tel 9)

theorem j2_x_check : powC14 j2oneC 3 j2X1 = j2oneC ∧ j2X1 ≠ j2oneC ∧
    powC14 j2oneC 3 j2X2 = j2oneC ∧
    (∀ a < 3, mul14 (powC14 j2oneC a j2X1) j2X2 = mul14 j2X2 (powC14 j2oneC a j2X1)) ∧
    ∀ a < 3, ∀ b < 3, 0 < b → powC14 j2oneC b j2X2 ≠ powC14 j2oneC a j2X1 := by
  decide +kernel

@[expose] def j2CentCount (y : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 9 × Fin 128)).filter fun q =>
    mul14 (mul14 (j2CC q.1) (j2Tel q.2)) y = mul14 y (mul14 (j2CC q.1) (j2Tel q.2))).card

theorem j2_cent_check₁ : j2CentCount j2X1 = 72 := by decide +kernel

theorem j2_cent_check₂ : j2CentCount j2X2 = 36 := by decide +kernel

theorem j2_cent_check₃ : j2CentCount (mul14 j2X1 j2X2) = 9 := by decide +kernel

theorem j2_cent_check₄ : j2CentCount (mul14 j2X1 (mul14 j2X2 j2X2)) = 36 := by decide +kernel

@[expose] def j2ZC (a b : ℕ) : ℕ := mul14 (powC14 j2oneC a j2X1) (powC14 j2oneC b j2X2)

theorem j2_rel_check : j2ZC 0 1 = j2X2 ∧ mul14 (j2ZC 0 2) j2X2 = j2oneC ∧
    j2ZC 1 1 = mul14 j2X1 j2X2 ∧ mul14 (j2ZC 2 2) (mul14 j2X1 j2X2) = j2oneC ∧
    j2ZC 1 2 = mul14 j2X1 (mul14 j2X2 j2X2) ∧
    mul14 (j2ZC 2 1) (mul14 j2X1 (mul14 j2X2 j2X2)) = j2oneC := by
  decide +kernel

theorem j2_three_check : powC14 j2oneC 3 j2bC = j2oneC ∧ j2bC ≠ j2oneC := by decide +kernel

end CFSG.Quasithin.F134
