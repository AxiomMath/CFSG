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

@[expose] def babyM : Fin 10 → Fin 10 → ℕ := ![
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![93150, 925, 63, 15, 1, 0, 0, 0, 0, 0],
    ![0, 4928, 63, 120, 42, 1, 0, 0, 0, 0],
    ![0, 42240, 4320, 1815, 420, 30, 15, 0, 0, 0],
    ![0, 45056, 24192, 6720, 1807, 272, 120, 891, 27, 0],
    ![0, 0, 64512, 53760, 30464, 10287, 5040, 24948, 3060, 3850],
    ![0, 0, 0, 30720, 15360, 5760, 3495, 0, 4320, 4125],
    ![0, 0, 0, 0, 2048, 512, 0, 891, 36, 100],
    ![0, 0, 0, 0, 43008, 43520, 53760, 24948, 53451, 53900],
    ![0, 0, 0, 0, 0, 32768, 30720, 41472, 32256, 31175]]

@[expose] def babyL : ℕ := 93150

@[expose] def babySizes : Fin 10 → ℕ :=
  ![1, 93150, 7_286_400, 262_310_400, 4_196_966_400, 470_060_236_800, 537_211_699_200,
    9_646_899_200, 6_685_301_145_600, 4_000_762_036_224]

@[expose] def babyTotal : ℕ := 11_707_448_673_375

theorem babyM_col_sum (i : Fin 10) : ∑ t, babyM t i = babyL := by
  fin_cases i <;> simp [Fin.sum_univ_succ, babyM, babyL]

theorem babySizes_balance (t : Fin 10) :
    ∑ i, babyM t i * babySizes i = babyL * babySizes t := by
  fin_cases t <;> simp [Fin.sum_univ_succ, babyM, babyL, babySizes]

theorem sum_babySizes : ∑ i, babySizes i = babyTotal := by
  simp [Fin.sum_univ_succ, babySizes, babyTotal]

theorem eq_babySizes_of_balance (s : Fin 10 → ℕ)
    (hs : ∀ t, ∑ i, babyM t i * s i = babyL * s t) (h0 : s 0 = 1) : s = babySizes := by
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
  simp [Fin.sum_univ_succ, babyM, babyL] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  zify at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  have h0' : (s 0 : ℤ) = 1 := by exact_mod_cast h0
  have h1 : (s 1 : ℤ) = 93150 := by linarith
  have h2 : (s 2 : ℤ) = 7_286_400 := by linarith
  have h3 : (s 3 : ℤ) = 262_310_400 := by linarith
  have h4 : (s 4 : ℤ) = 4_196_966_400 := by linarith
  have h5 : (s 5 : ℤ) = 470_060_236_800 := by linarith
  have h6 : (s 6 : ℤ) = 537_211_699_200 := by linarith
  have h7 : (s 7 : ℤ) = 9_646_899_200 := by linarith
  have h8 : (s 8 : ℤ) = 6_685_301_145_600 := by linarith
  have h9 : (s 9 : ℤ) = 4_000_762_036_224 := by linarith
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

theorem sum_eq_babyTotal_of_balance (s : Fin 10 → ℕ)
    (hs : ∀ t, ∑ i, babyM t i * s i = babyL * s t) (h0 : s 0 = 1) :
    ∑ i, s i = babyTotal := by
  rw [eq_babySizes_of_balance s hs h0]
  exact sum_babySizes

section Application

variable {G X : Type*} [Group G] [MulAction G X] {R : Fin 10 → Type*} [∀ i, Fintype (R i)]

theorem Setup.card_orb_eq_babySizes (S : Setup G X (Fin 10) R) [Finite S.H]
    (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i))) (hO : Function.Injective S.orb)
    (hM : S.M = babyM) (hL : S.L = babyL) (h0 : Nat.card (S.orb 0) = 1) :
    (∀ i, Nat.card (S.orb i) = babySizes i) ∧ Nat.card S.X0 = babyTotal := by
  have hs : ∀ t, ∑ i, babyM t i * Nat.card (S.orb i) = babyL * Nat.card (S.orb t) := by
    intro t
    have h := S.sum_transition_eq hD hO t
    rwa [hM, hL] at h
  refine ⟨fun i => congrFun (eq_babySizes_of_balance (fun i => Nat.card (S.orb i)) hs h0) i, ?_⟩
  rw [S.card_X0_eq_sum hO]
  exact sum_eq_babyTotal_of_balance _ hs h0

end Application

end CFSG.Monster.AxisCount
