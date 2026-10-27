module

public import CFSG.Quasithin.Vol2.F134RuTables

public section

namespace CFSG.Quasithin.F134

theorem ru_tgen_check : ∀ k < 3, (∀ c ∈ ruTGenW.getD k [], c < 2) ∧
    ruWordC (ruTGenW.getD k []) = ruTG k := by
  decide +kernel

theorem ru_x_check : ∀ p < 14, (∀ c ∈ ruXW.getD p [], c < 3) ∧
    ruTWordC (ruXW.getD p []) = ruXC p := by
  decide +kernel

@[expose] def ruTAFold (a : ℕ) : ℕ :=
  (List.range 7).foldl (fun acc p => bif a.testBit p then mulF28 acc (ruXC p) else acc) ruOneC

@[expose] def ruTBFold (b : ℕ) : ℕ :=
  (List.range 7).foldl (fun acc p => bif b.testBit p then mulF28 acc (ruXC (7 + p)) else acc)
    ruOneC

theorem ru_ta_check : ∀ a < 128, ruTAFold a = ruTAC a := by decide +kernel

theorem ru_tb_check : ∀ b < 128, ruTBFold b = ruTBC b := by decide +kernel

theorem ru_sq_check : ∀ p < 14, ruSq p < 16384 ∧ (∀ q < p + 1, (ruSq p).testBit q = false) ∧
    mulF28 (ruXC p) (ruXC p) = ruNFC (ruSq p) := by
  decide +kernel

theorem ru_cj_check : ∀ i < 14, ∀ j < 14, i < j → ruCj i j < 16384 ∧
    (∀ q < i + 1, (ruCj i j).testBit q = false) ∧
    mulF28 (ruXC j) (ruXC i) = mulF28 (ruXC i) (ruNFC (ruCj i j)) := by
  decide +kernel

theorem ru_tnf_check : ∀ k < 3, ruTnf k < 16384 ∧ ruTG k = ruNFC (ruTnf k) := by
  decide +kernel

theorem ru_g_check : ∀ c < 2, (∀ x ∈ ruGW.getD c [], x < 2) ∧
    ruWordC (ruGW.getD c []) = ruG c := by
  decide +kernel

theorem ru_ab_check : ruLWordC ruAW = ruAC ∧ (∀ l ∈ ruAW, l < 16386) ∧
    ruLWordC ruBW = ruBC ∧ ∀ l ∈ ruBW, l < 16386 := by
  decide +kernel

theorem ru_dw_zero : ruDW.getD 0 [] = [] := by decide +kernel

theorem ru_gcl_check : ∀ c < 2, 0 < ruM c ∧ ruR c 0 = 0 ∧ ∀ k < 3, ∀ s < ruM c,
    ruCL c (ruM c * k + s) / 16384 < ruM c ∧ ruR c s < 16384 ∧
    ruR c (ruCL c (ruM c * k + s) / 16384) < 16384 ∧
    mulF28 (mulF28 (ruTG k) (ruNFC (ruR c s))) (ruG c) =
      mulF28 (mulF28 (ruNFC (ruR c (ruCL c (ruM c * k + s) / 16384))) (ruG c))
        (ruNFC (ruCL c (ruM c * k + s) % 16384)) := by
  decide +kernel

theorem ru_cos_check : ∀ i < 2, ruCR (i + 1) 0 = 0 ∧ ∀ k < 3, ∀ r < 2,
    ruCosE (i + 1) (2 * k + r) / 16384 < 2 ∧ ruCR (i + 1) r < 16384 ∧
    ruCR (i + 1) (ruCosE (i + 1) (2 * k + r) / 16384) < 16384 ∧
    mulF28 (mulF28 (ruTG k) (ruNFC (ruCR (i + 1) r))) (ruD (i + 1)) =
      mulF28 (mulF28 (ruNFC (ruCR (i + 1) (ruCosE (i + 1) (2 * k + r) / 16384))) (ruD (i + 1)))
        (ruNFC (ruCosE (i + 1) (2 * k + r) % 16384)) := by
  decide +kernel

theorem ru_three_check : (∀ l ∈ ruThreeW, l < 16386) ∧
    mulF28 (ruLWordC ruThreeW) (mulF28 (ruLWordC ruThreeW) (ruLWordC ruThreeW)) = ruOneC ∧
    ruLWordC ruThreeW ≠ ruOneC := by
  decide +kernel

end CFSG.Quasithin.F134
