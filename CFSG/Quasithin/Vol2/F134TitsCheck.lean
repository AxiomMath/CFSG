module

public import CFSG.Quasithin.Vol2.F134TitsTables

public section

namespace CFSG.Quasithin.F134

theorem tits_rho_check : ∀ i < 10, titsRC i < 2 ^ (26 * 26) ∧ 0 < titsOrd i ∧
    titsPow (titsOrd i) (titsRC i) = titsOneC := by
  decide +kernel

theorem tits_rinv_check : ∀ i < 10, titsRInvC i < 2 ^ (26 * 26) ∧
    mulF26 (titsRC i) (titsRInvC i) = titsOneC ∧ mulF26 (titsRInvC i) (titsRC i) = titsOneC := by
  decide +kernel

theorem tits_rho_ne_one : titsRC 0 ≠ titsOneC := by decide +kernel

theorem tits_one_check : titsOneC < 2 ^ (26 * 26) ∧
    matCode26 (1 : Matrix (Fin 26) (Fin 26) (ZMod 2)) = titsOneC := by
  decide +kernel

theorem tits_tgen_check : ∀ k < 2, (∀ c ∈ titsTGenW.getD k [], c < 10) ∧
    titsWordC (titsTGenW.getD k []) = titsTG k := by
  decide +kernel

theorem tits_x_check : ∀ p < 11, (∀ c ∈ titsXW.getD p [], c < 2) ∧
    titsTWordC (titsXW.getD p []) = titsXC p := by
  decide +kernel

@[expose] def titsTAFold (a : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc p => bif a.testBit p then mulF26 acc (titsXC p) else acc)
    titsOneC

@[expose] def titsTBFold (b : ℕ) : ℕ :=
  (List.range 5).foldl (fun acc p => bif b.testBit p then mulF26 acc (titsXC (6 + p)) else acc)
    titsOneC

theorem tits_ta_check : ∀ a < 64, titsTAFold a = titsTAC a := by decide +kernel

theorem tits_tb_check : ∀ b < 32, titsTBFold b = titsTBC b := by decide +kernel

theorem tits_sq_check : ∀ p < 11, titsSq p < 2048 ∧ (∀ q < p + 1, (titsSq p).testBit q = false) ∧
    mulF26 (titsXC p) (titsXC p) = titsNFC (titsSq p) := by
  decide +kernel

theorem tits_cj_check : ∀ i < 11, ∀ j < 11, i < j → titsCj i j < 2048 ∧
    (∀ q < i + 1, (titsCj i j).testBit q = false) ∧
    mulF26 (titsXC j) (titsXC i) = mulF26 (titsXC i) (titsNFC (titsCj i j)) := by
  decide +kernel

theorem tits_tnf_check : ∀ k < 2, titsTnf k < 2048 ∧ titsTG k = titsNFC (titsTnf k) := by
  decide +kernel

theorem tits_rnf_check : ∀ i < 10, 2 ≤ i → titsRnf i < 2048 ∧ titsRC i = titsNFC (titsRnf i) := by
  decide +kernel

theorem tits_d_check : titsDW.getD 0 [] = [] ∧ titsDW.getD 1 [] = [1] ∧
    ∀ j < 18, (∀ c ∈ titsDW.getD j [], c < 10) ∧ titsWordC (titsDW.getD j []) = titsDC j := by
  decide +kernel

theorem tits_gcl_check : ∀ c < 2, 0 < titsM c ∧ titsR c 0 = 0 ∧ ∀ k < 2, ∀ s < titsM c,
    titsCL c (titsM c * k + s) / 2048 < titsM c ∧ titsR c s < 2048 ∧
    titsR c (titsCL c (titsM c * k + s) / 2048) < 2048 ∧
    mulF26 (mulF26 (titsTG k) (titsNFC (titsR c s))) (titsRC c) =
      mulF26 (mulF26 (titsNFC (titsR c (titsCL c (titsM c * k + s) / 2048))) (titsRC c))
        (titsNFC (titsCL c (titsM c * k + s) % 2048)) := by
  decide +kernel

theorem tits_gdec_check : ∀ c < 2, ∀ j < 18, ∀ s < titsM c,
    titsDec c (titsM c * j + s) / 4194304 < 18 ∧ titsR c s < 2048 ∧
    mulF26 (mulF26 (titsDC j) (titsNFC (titsR c s))) (titsRC c) =
      mulF26 (mulF26 (titsNFC (titsDec c (titsM c * j + s) / 2048 % 2048))
        (titsDC (titsDec c (titsM c * j + s) / 4194304)))
        (titsNFC (titsDec c (titsM c * j + s) % 2048)) := by
  decide +kernel

theorem tits_bad_check : ∀ j < 18, 2 ≤ j →
    (titsBad j % 32 = 5 ∨ titsBad j % 32 = 13) ∧ titsBad j / 1024 < 2048 ∧
    titsPow (titsBad j % 32)
        (titsPow (titsBad j / 32 % 32) (mulF26 (titsDC j) (titsNFC (titsBad j / 1024)))) =
      titsOneC ∧
    titsPow (titsBad j / 32 % 32) (mulF26 (titsDC j) (titsNFC (titsBad j / 1024))) ≠ titsOneC := by
  decide +kernel

end CFSG.Quasithin.F134
