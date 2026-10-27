module

public import CFSG.Monster.AxisCount.Abstract
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Monster.AxisCount

@[expose] def transM : Fin 12 → Fin 12 → ℕ := ![
    ![93150, 135, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![8197200, 64935, 3542, 63, 15, 0, 0, 0, 0, 0, 0, 0],
    ![8294400, 483840, 35927, 2232, 240, 891, 27, 1, 0, 0, 0, 0],
    ![0, 7741440, 2007808, 137367, 33600, 74844, 7452, 660, 0, 3850, 60, 198],
    ![0, 8294400, 971520, 151200, 54255, 0, 12960, 330, 2295, 4125, 1275, 945],
    ![0, 0, 1036288, 96768, 0, 133731, 8748, 1848, 0, 2300, 0, 198],
    ![0, 0, 7254016, 2225664, 860160, 2020788, 321003, 134024, 0, 284900, 59520, 72450],
    ![0, 0, 5275648, 3870720, 430080, 8382528, 2631744, 2217999, 483840, 3010000, 1375680, 1399104],
    ![0, 0, 0, 0, 522240, 0, 0, 84480, 486135, 0, 271200, 274320],
    ![0, 0, 0, 2064384, 491520, 953856, 511488, 275200, 0, 411775, 131520, 106992],
    ![0, 0, 0, 1548288, 7311360, 0, 5142528, 6052992, 6834240, 6329400, 6435735, 6543936],
    ![0, 0, 0, 6488064, 6881280, 5018112, 7948800, 7817216, 8778240, 6538400, 8309760, 8186607]]

@[expose] def transL : ℕ := 16_584_750

@[expose] def orbitSizes : Fin 12 → ℕ :=
  ![196560, 11_935_123_200, 1_630_347_264_000, 1_466_587_938_816_000, 6_599_645_724_672_000,
    1_896_194_506_752_000, 438_020_931_059_712_000, 8_601_138_282_627_072_000,
    1_501_786_049_347_584_000, 786_389_785_840_189_440, 37_845_008_443_559_116_800,
    48_057_153_579_122_688_000]

@[expose] def totalAxes : ℕ := 97_239_461_142_009_186_000

theorem transL_eq : transL = 2 * 8292375 := rfl

theorem transM_col_sum (i : Fin 12) : ∑ t, transM t i = transL := by
  fin_cases i <;> simp [Fin.sum_univ_succ, transM, transL]

theorem orbitSizes_balance (t : Fin 12) :
    ∑ i, transM t i * orbitSizes i = transL * orbitSizes t := by
  fin_cases t <;> simp [Fin.sum_univ_succ, transM, transL, orbitSizes]

theorem sum_orbitSizes : ∑ i, orbitSizes i = totalAxes := by
  simp [Fin.sum_univ_succ, orbitSizes, totalAxes]

theorem eq_orbitSizes_of_balance (s : Fin 12 → ℕ)
    (hs : ∀ t, ∑ i, transM t i * s i = transL * s t) (h0 : s 0 = 196560) : s = orbitSizes := by
  have e0 := hs 0
  have e1 := hs 1
  have e2 := hs 2
  have e3 := hs 3
  have e4 := hs 4
  have e5 := hs 5
  have e6 := hs 6
  have e7 := hs 7
  have e8 := hs 8
  have e9 := hs 9
  have e10 := hs 10
  have e11 := hs 11
  simp [Fin.sum_univ_succ, transM, transL] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  zify at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  have h0' : (s 0 : ℤ) = 196560 := by exact_mod_cast h0
  have h1 : (s 1 : ℤ) = 11_935_123_200 := by linarith
  have h2 : (s 2 : ℤ) = 1_630_347_264_000 := by linarith
  have h3 : (s 3 : ℤ) = 1_466_587_938_816_000 := by linarith
  have h4 : (s 4 : ℤ) = 6_599_645_724_672_000 := by linarith
  have h5 : (s 5 : ℤ) = 1_896_194_506_752_000 := by linarith
  have h6 : (s 6 : ℤ) = 438_020_931_059_712_000 := by linarith
  have h7 : (s 7 : ℤ) = 8_601_138_282_627_072_000 := by linarith
  have h8 : (s 8 : ℤ) = 1_501_786_049_347_584_000 := by linarith
  have h9 : (s 9 : ℤ) = 786_389_785_840_189_440 := by linarith
  have h10 : (s 10 : ℤ) = 37_845_008_443_559_116_800 := by linarith
  have h11 : (s 11 : ℤ) = 48_057_153_579_122_688_000 := by linarith
  funext i
  fin_cases i
  · exact h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7
  · exact_mod_cast h8
  · exact_mod_cast h9
  · exact_mod_cast h10
  · exact_mod_cast h11

theorem sum_eq_totalAxes_of_balance (s : Fin 12 → ℕ)
    (hs : ∀ t, ∑ i, transM t i * s i = transL * s t) (h0 : s 0 = 196560) :
    ∑ i, s i = totalAxes := by
  rw [eq_orbitSizes_of_balance s hs h0]
  exact sum_orbitSizes

section Application

variable {G X : Type*} [Group G] [MulAction G X] {R : Fin 12 → Type*} [∀ i, Fintype (R i)]

theorem Setup.card_orb_eq_orbitSizes (S : Setup G X (Fin 12) R) [Finite S.H]
    (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i))) (hO : Function.Injective S.orb)
    (hM : S.M = transM) (hL : S.L = transL) (h0 : Nat.card (S.orb 0) = 196560) :
    (∀ i, Nat.card (S.orb i) = orbitSizes i) ∧ Nat.card S.X0 = totalAxes := by
  have hs : ∀ t, ∑ i, transM t i * Nat.card (S.orb i) = transL * Nat.card (S.orb t) := by
    intro t
    have h := S.sum_transition_eq hD hO t
    rwa [hM, hL] at h
  refine ⟨fun i => congrFun (eq_orbitSizes_of_balance (fun i => Nat.card (S.orb i)) hs h0) i, ?_⟩
  rw [S.card_X0_eq_sum hO]
  exact sum_eq_totalAxes_of_balance _ hs h0

end Application

end CFSG.Monster.AxisCount
