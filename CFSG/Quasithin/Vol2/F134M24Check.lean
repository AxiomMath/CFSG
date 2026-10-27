module

public import CFSG.Quasithin.Vol2.F134M24Tables

public section

namespace CFSG.Quasithin.F134

open Equiv

theorem m24_code_a : permCode m24PermA = m24aC := by decide +kernel

theorem m24_code_b : permCode m24PermB = m24bC := by decide +kernel

theorem m24_code_one : permCode (1 : Perm (Fin 24)) = m24oneC := by decide +kernel

theorem m24_tel_zero : m24Tel 0 = m24oneC := by decide +kernel

theorem m24_tgen_check : ∀ k < 4, m24WordC (m24TGenW.getD k []) = m24TG k := by decide +kernel

theorem m24_nxt_check : ∀ i < 1024, ∀ k < 4, m24Nxt (4 * i + k) < 1024 ∧
    mul24 (m24Tel i) (m24TG k) = m24Tel (m24Nxt (4 * i + k)) := by
  decide +kernel

theorem m24_par_check : ∀ i < 1024, 0 < i → m24Par i / 8 < i ∧ m24Par i % 8 < 4 ∧
    mul24 (m24Tel (m24Par i / 8)) (m24TG (m24Par i % 8)) = m24Tel i := by
  decide +kernel

theorem m24_pow_check : ∀ i < 1024, sqC24 3 (m24Tel i) = m24oneC := by decide +kernel

theorem m24_center_check :
    (∀ k < 4, mul24 (m24Tel m24Z0) (m24TG k) = mul24 (m24TG k) (m24Tel m24Z0)) ∧
    ∀ i < 1024, (∀ k < 4, mul24 (m24Tel i) (m24TG k) = mul24 (m24TG k) (m24Tel i)) →
      i = 0 ∨ i = m24Z0 := by
  decide +kernel

theorem m24_g_check : ∀ c < 3, m24WordC (m24GW.getD c []) = m24G c := by decide +kernel

theorem m24_dw_zero : m24DW.getD 0 [] = [] := by decide +kernel

theorem m24_d_check : ∀ j < 510, m24LWordC (m24DW.getD j []) = m24D j ∧
    ∀ l ∈ m24DW.getD j [], l < 1027 := by
  decide +kernel

theorem m24_ab_check : m24LWordC m24AW = m24aC ∧ (∀ l ∈ m24AW, l < 1027) ∧
    m24LWordC m24BW = m24bC ∧ ∀ l ∈ m24BW, l < 1027 := by
  decide +kernel

theorem m24_gconj_check : ∀ c < 3, ∀ l < (m24GUL.getD c []).length,
    (m24GUL.getD c []).getD l 0 < 1024 ∧ (m24GCL.getD c []).getD l 0 < 1024 ∧
    mul24 (m24Tel ((m24GUL.getD c []).getD l 0)) (m24G c) =
      mul24 (m24G c) (m24Tel ((m24GCL.getD c []).getD l 0)) := by
  decide +kernel

theorem m24_gtree_check : ∀ c < 3, m24GEAt c 0 = 0 ∧ ∀ p < 512, m24GEAt c p < 1024 ∧ (0 < p →
    m24GPAt c p / 8 < p ∧ m24GPAt c p % 8 < (m24GUL.getD c []).length ∧
    mul24 (m24Tel (m24GEAt c (m24GPAt c p / 8)))
      (m24Tel ((m24GUL.getD c []).getD (m24GPAt c p % 8) 0)) = m24Tel (m24GEAt c p)) := by
  decide +kernel

theorem m24_gtrans_check : ∀ c < 3, ∀ i < 1024, m24GQAt c i / 512 < 2 ∧
    m24GQAt c i % 512 < 512 ∧ (m24GRL.getD c []).getD (m24GQAt c i / 512) 0 < 1024 ∧
    m24Tel i = mul24 (m24Tel ((m24GRL.getD c []).getD (m24GQAt c i / 512) 0))
      (m24Tel (m24GEAt c (m24GQAt c i % 512))) := by
  decide +kernel

theorem m24_bad_check : ∀ j < 510, 8 ≤ j →
    (m24Bad j % 16 = 5 ∨ m24Bad j % 16 = 7) ∧ m24Bad j / 256 < 1024 ∧
      powC24 m24oneC (m24Bad j % 16)
          (powC24 m24oneC (m24Bad j / 16 % 16) (mul24 (m24D j) (m24Tel (m24Bad j / 256)))) =
        m24oneC ∧
      powC24 m24oneC (m24Bad j / 16 % 16) (mul24 (m24D j) (m24Tel (m24Bad j / 256))) ≠
        m24oneC := by
  decide +kernel

theorem m24_cos_check : ∀ j < 8, 0 < j → m24CR j 0 = 0 ∧ ∀ i < 1024,
    m24Cos j i / 1024 < m24CN j ∧ m24CR j (m24Cos j i / 1024) < 1024 ∧
    mul24 (m24Tel i) (m24D j) =
      mul24 (mul24 (m24Tel (m24CR j (m24Cos j i / 1024))) (m24D j))
        (m24Tel (m24Cos j i % 1024)) := by
  decide +kernel

theorem m24_excl_check : ∀ e < 10,
    (m24Excl e % 16 = 5 ∨ m24Excl e % 16 = 7) ∧ m24Excl e / 256 < 1024 ∧
      powC24 m24oneC (m24Excl e % 16) (powC24 m24oneC (m24Excl e / 16 % 16)
        (mul24 (mul24 (m24D (m24EP e / 8)) (m24Tel (m24Excl e / 256))) (m24D (m24EP e % 8)))) =
        m24oneC ∧
      powC24 m24oneC (m24Excl e / 16 % 16)
        (mul24 (mul24 (m24D (m24EP e / 8)) (m24Tel (m24Excl e / 256))) (m24D (m24EP e % 8))) ≠
        m24oneC := by
  decide +kernel

theorem m24_ep_check : m24ExclP = [41, 44, 46, 47, 50, 51, 55, 58, 60, 10] := by decide +kernel

theorem m24_hcs_check : ∀ X < 4, m24HC X 0 = 0 ∧ (∀ s < 9, m24HC X s / 1024 < 8) ∧
    ∀ j < 8, 0 < j → (m24HJ.getD X []).contains j = true → ∀ b < m24CN j,
      ∃ s < 9, m24HC X s = 1024 * j + m24CR j b := by
  decide +kernel

theorem m24_x_check : ∀ X < 3, (m24HX.getD X []).getD 0 0 / 1024 < 9 ∧
    (m24HX.getD X []).getD 1 0 / 1024 < 9 ∧ powC24 m24oneC 3 (m24XC X 0) = m24oneC ∧
    m24XC X 0 ≠ m24oneC ∧ powC24 m24oneC 3 (m24XC X 1) = m24oneC ∧
    mul24 (m24XC X 0) (m24XC X 1) = mul24 (m24XC X 1) (m24XC X 0) ∧
    ∀ a < 3, ∀ b < 3, 0 < b → powC24 m24oneC b (m24XC X 1) ≠ powC24 m24oneC a (m24XC X 0) := by
  decide +kernel

theorem m24_z_check : ∀ X < 2,
    mul24 (m24XC X 0) (m24Tel m24Z0) = mul24 (m24Tel m24Z0) (m24XC X 0) ∧
    mul24 (m24XC X 1) (m24Tel m24Z0) ≠ mul24 (m24Tel m24Z0) (m24XC X 1) := by
  decide +kernel

@[expose] def m24YC (e : ℕ) : ℕ :=
  if e = 0 then m24XC 2 1 else if e = 1 then mul24 (m24XC 2 0) (m24XC 2 1)
    else mul24 (m24XC 2 0) (mul24 (m24XC 2 1) (m24XC 2 1))

theorem m24_psi_check : ∀ e < 3, (∀ l ∈ m24PsiW.getD e [], l < 1027) ∧
    powC24 m24oneC 7 (m24LWordC (m24PsiW.getD e [])) = m24oneC ∧
    m24LWordC (m24PsiW.getD e []) ≠ m24oneC ∧
    mul24 (m24LWordC (m24PsiW.getD e [])) (m24YC e) =
      mul24 (m24YC e) (m24LWordC (m24PsiW.getD e [])) := by
  decide +kernel

theorem m24_psi_rel_check : ∀ a < 3, ∀ b < 3, 0 < b → ∃ e < 3, ∃ m < 3,
    m24ZC 2 a b = powC24 m24oneC m (m24YC e) := by
  decide +kernel

theorem m24_fix_check :
    ((Finset.range 24).filter fun i => digW 5 (m24XC 2 0) i = i).card = 6 := by
  decide +kernel

theorem m24_three_check : powC24 m24oneC 3 m24bC = m24oneC ∧ m24bC ≠ m24oneC := by
  decide +kernel

end CFSG.Quasithin.F134
