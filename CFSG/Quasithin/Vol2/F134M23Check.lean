module

public import CFSG.Quasithin.Vol2.F134M23Tables

public section

namespace CFSG.Quasithin.F134

open Equiv

theorem m23_code_a : permCode m23PermA = m23aC := by decide +kernel

theorem m23_code_b : permCode m23PermB = m23bC := by decide +kernel

theorem m23_code_one : permCode (1 : Perm (Fin 23)) = m23oneC := by decide +kernel

theorem m23_tel_zero : m23Tel 0 = m23oneC := by decide +kernel

theorem m23_tgen_check : ∀ k < 3, m23WordC (m23TGenW.getD k []) = m23TG k := by decide +kernel

theorem m23_nxt_check : ∀ i < 128, ∀ k < 3, m23Nxt (3 * i + k) < 128 ∧
    mul23 (m23Tel i) (m23TG k) = m23Tel (m23Nxt (3 * i + k)) := by
  decide +kernel

theorem m23_par_check : ∀ i < 128, 0 < i → m23Par i / 4 < i ∧ m23Par i % 4 < 3 ∧
    mul23 (m23Tel (m23Par i / 4)) (m23TG (m23Par i % 4)) = m23Tel i := by
  decide +kernel

theorem m23_pow_check : ∀ i < 128, sqC23 3 (m23Tel i) = m23oneC := by decide +kernel

theorem m23_tel_ne : ∀ i < 128, ∀ j < i, m23Tel i ≠ m23Tel j := by decide +kernel

theorem m23_g_check : ∀ c < 2, m23WordC (m23GW.getD c []) = m23G c := by decide +kernel

theorem m23_dw_zero : m23DW.getD 0 [] = [] := by decide +kernel

theorem m23_d_check₀ : ∀ j < 420, m23LWordC (m23DW.getD j []) = m23D j ∧
    ∀ l ∈ m23DW.getD j [], l < 130 := by
  decide +kernel

theorem m23_d_check₁ : ∀ j < 415, m23LWordC (m23DW.getD (j + 420) []) = m23D (j + 420) ∧
    ∀ l ∈ m23DW.getD (j + 420) [], l < 130 := by
  decide +kernel

theorem m23_d_check : ∀ j < 835, m23LWordC (m23DW.getD j []) = m23D j ∧
    ∀ l ∈ m23DW.getD j [], l < 130 := by
  intro j hj
  rcases Nat.lt_or_ge j 420 with h | h
  · exact m23_d_check₀ j h
  · have := m23_d_check₁ (j - 420) (by omega)
    rwa [Nat.sub_add_cancel h] at this

theorem m23_ab_check : m23LWordC m23AW = m23aC ∧ (∀ l ∈ m23AW, l < 130) ∧
    m23LWordC m23BW = m23bC ∧ ∀ l ∈ m23BW, l < 130 := by
  decide +kernel

theorem m23_gconj_check : ∀ c < 2, ∀ l < 3, (m23GUL.getD c []).getD l 0 < 128 ∧
    (m23GCL.getD c []).getD l 0 < 128 ∧
    mul23 (m23Tel ((m23GUL.getD c []).getD l 0)) (m23G c) =
      mul23 (m23G c) (m23Tel ((m23GCL.getD c []).getD l 0)) := by
  decide +kernel

theorem m23_gtree_check : ∀ c < 2, m23GEAt c 0 = 0 ∧ ∀ p < 32, m23GEAt c p < 128 ∧ (0 < p →
    m23GPAt c p / 8 < p ∧ m23GPAt c p % 8 < 3 ∧
    mul23 (m23Tel (m23GEAt c (m23GPAt c p / 8)))
      (m23Tel ((m23GUL.getD c []).getD (m23GPAt c p % 8) 0)) = m23Tel (m23GEAt c p)) := by
  decide +kernel

theorem m23_gtrans_check : ∀ c < 2, ∀ i < 128, m23GQAt c i / 128 < 4 ∧ m23GQAt c i % 128 < 32 ∧
    (m23GRL.getD c []).getD (m23GQAt c i / 128) 0 < 128 ∧
    m23Tel i = mul23 (m23Tel ((m23GRL.getD c []).getD (m23GQAt c i / 128) 0))
      (m23Tel (m23GEAt c (m23GQAt c i % 128))) := by
  decide +kernel

theorem m23_bad_check : ∀ j < 835, 6 ≤ j →
    (m23Bad j % 16 = 5 ∨ m23Bad j % 16 = 7) ∧ m23Bad j / 256 < 128 ∧
      powC23 m23oneC (m23Bad j % 16)
          (powC23 m23oneC (m23Bad j / 16 % 16) (mul23 (m23D j) (m23Tel (m23Bad j / 256)))) =
        m23oneC ∧
      powC23 m23oneC (m23Bad j / 16 % 16) (mul23 (m23D j) (m23Tel (m23Bad j / 256))) ≠
        m23oneC := by
  decide +kernel

theorem m23_cos_check : ∀ j < 6, 0 < j → ∀ i < 128, m23Cos j i / 128 < 2 ∧
    mul23 (m23Tel i) (m23D j) =
      mul23 (mul23 (m23Tel (if m23Cos j i / 128 = 0 then 0 else 1)) (m23D j))
        (m23Tel (m23Cos j i % 128)) := by
  decide +kernel

theorem m23_excl_check : ∀ k < 5, 0 < k →
    (m23Excl k % 16 = 5 ∨ m23Excl k % 16 = 7) ∧ m23Excl k / 256 < 128 ∧
      powC23 m23oneC (m23Excl k % 16) (powC23 m23oneC (m23Excl k / 16 % 16)
        (mul23 (mul23 (m23D 5) (m23Tel (m23Excl k / 256))) (m23D k))) = m23oneC ∧
      powC23 m23oneC (m23Excl k / 16 % 16)
        (mul23 (mul23 (m23D 5) (m23Tel (m23Excl k / 256))) (m23D k)) ≠ m23oneC := by
  decide +kernel

@[expose] def m23CC (s : ℕ) : ℕ :=
  if s = 0 then m23oneC else mul23 (m23Tel (if s % 2 = 0 then 1 else 0)) (m23D ((s + 1) / 2))

@[expose] def m23X1 : ℕ := mul23 (m23D 1) (m23Tel 1)

@[expose] def m23X2 : ℕ := mul23 (m23D 2) (m23Tel 115)

theorem m23_x_check : powC23 m23oneC 3 m23X1 = m23oneC ∧ m23X1 ≠ m23oneC ∧
    powC23 m23oneC 3 m23X2 = m23oneC ∧
    (∀ a < 3, mul23 (powC23 m23oneC a m23X1) m23X2 = mul23 m23X2 (powC23 m23oneC a m23X1)) ∧
    ∀ a < 3, ∀ b < 3, 0 < b → powC23 m23oneC b m23X2 ≠ powC23 m23oneC a m23X1 := by
  decide +kernel

@[expose] def m23CentCount (y : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 9 × Fin 128)).filter fun q =>
    mul23 (mul23 (m23CC q.1) (m23Tel q.2)) y = mul23 y (mul23 (m23CC q.1) (m23Tel q.2))).card

theorem m23_cent_check₁ : m23CentCount m23X1 = 9 := by decide +kernel

theorem m23_cent_check₂ : m23CentCount m23X2 = 36 := by decide +kernel

theorem m23_cent_check₃ : m23CentCount (mul23 m23X1 m23X2) = 36 := by decide +kernel

theorem m23_cent_check₄ : m23CentCount (mul23 m23X1 (mul23 m23X2 m23X2)) = 36 := by
  decide +kernel

@[expose] def m23ZC (a b : ℕ) : ℕ := mul23 (powC23 m23oneC a m23X1) (powC23 m23oneC b m23X2)

theorem m23_rel_check : m23ZC 0 1 = m23X2 ∧ mul23 (m23ZC 0 2) m23X2 = m23oneC ∧
    m23ZC 1 1 = mul23 m23X1 m23X2 ∧ mul23 (m23ZC 2 2) (mul23 m23X1 m23X2) = m23oneC ∧
    m23ZC 1 2 = mul23 m23X1 (mul23 m23X2 m23X2) ∧
    mul23 (m23ZC 2 1) (mul23 m23X1 (mul23 m23X2 m23X2)) = m23oneC := by
  decide +kernel

theorem m23_three_check :
    powC23 m23oneC 3 (m23WordC m23ThreeW) = m23oneC ∧ m23WordC m23ThreeW ≠ m23oneC := by
  decide +kernel

end CFSG.Quasithin.F134
