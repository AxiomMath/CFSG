module

public import CFSG.Quasithin.Vol2.F134HSTables

public section

namespace CFSG.Quasithin.F134

theorem hs_let_check : hsLet 0 = hsAC ∧ ∀ c < 5, 0 < c → hsLet c = powC20 hsOneC c hsBC := by
  decide +kernel

theorem hs_tel_zero : hsTel 0 = hsOneC := by decide +kernel

theorem hs_dw_zero : hsDW.getD 0 [] = [] := by decide +kernel

theorem hs_tgen_check : ∀ k < 3, hsWordC (hsTGenW.getD k []) = hsTG k ∧
    ∀ c ∈ hsTGenW.getD k [], c < 5 := by
  decide +kernel

theorem hs_nxt_check : ∀ i < 512, ∀ k < 3, hsNxt (3 * i + k) < 512 ∧
    mulX20 (hsTel i) (hsTG k) = hsTel (hsNxt (3 * i + k)) := by
  decide +kernel

theorem hs_par_check : ∀ i < 512, 0 < i → hsPar i / 4 < i ∧ hsPar i % 4 < 3 ∧
    mulX20 (hsTel (hsPar i / 4)) (hsTG (hsPar i % 4)) = hsTel i := by
  decide +kernel

theorem hs_pow_check : ∀ i < 512, sqC20 9 (hsTel i) = hsOneC := by decide +kernel

theorem hs_a_check : hsTel 486 = hsAC := by decide +kernel

theorem hs_d_check : ∀ j < 270, hsWordC (hsDW.getD j []) = hsD j ∧
    ∀ c ∈ hsDW.getD j [], c < 5 := by
  decide +kernel

theorem hs_bad_check : ∀ j < 270, 3 ≤ j →
    (hsBad j % 16 = 5 ∨ hsBad j % 16 = 7 ∨ hsBad j % 16 = 11) ∧ hsBad j / 512 < 512 ∧
      powC20 hsOneC (hsBad j % 16)
          (powC20 hsOneC (hsBad j / 16 % 32) (mulX20 (hsD j) (hsTel (hsBad j / 512)))) =
        hsOneC ∧
      powC20 hsOneC (hsBad j / 16 % 32) (mulX20 (hsD j) (hsTel (hsBad j / 512))) ≠ hsOneC := by
  decide +kernel

theorem hs_cos_check : ∀ j < 3, 0 < j → ∀ i < 512, hsCos j i / 512 < 2 ∧
    mulX20 (hsTel i) (hsD j) =
      mulX20 (mulX20 (hsTel (if hsCos j i / 512 = 0 then 0 else if j = 1 then 3 else 1))
        (hsD j)) (hsTel (hsCos j i % 512)) := by
  decide +kernel

theorem hs_three_check : powC20 hsOneC 3 (hsWordC hsThreeW) = hsOneC ∧
    hsWordC hsThreeW ≠ hsOneC ∧ ∀ c ∈ hsThreeW, c < 5 := by
  decide +kernel

end CFSG.Quasithin.F134
