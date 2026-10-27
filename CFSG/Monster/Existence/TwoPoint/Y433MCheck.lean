module

public import CFSG.Monster.Existence.TwoPoint.Fi23S4Check

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def y433Sigma (c : ℕ) : ℕ := [3, 4, 5, 6, 9, 2, 1, 0, 7, 8].getD c 0

@[expose] def y433W (c : ℕ) : List Native.Gen :=
  if c = 10 then s4WGamma else fiWU[y433Sigma c]!

@[expose] def y433P (c : ℕ) : List Native.PGen :=
  if c = 10 then s4PGamma else fiPU[y433Sigma c]!

theorem y433Sigma_lt {c : ℕ} (hc : c < 10) : y433Sigma c < 10 := by
  have : ∀ c < 10, y433Sigma c < 10 := by decide
  exact this c hc

theorem y433P_eq {c : ℕ} (hc : c < 11) : y433P c = HS.pw (y433W c) := by
  unfold y433P y433W
  by_cases h10 : c = 10
  · rw [ite_eq_left h10, ite_eq_left h10]
    rfl
  · rw [ite_eq_right h10, ite_eq_right h10]
    exact fiPU_get (y433Sigma_lt (by omega))

@[expose] def y433RelW (R : List ℕ) : List Native.Gen := (R.reverse.map y433W).flatten

@[expose] def y433RelP (R : List ℕ) : List Native.PGen := (R.reverse.map y433P).flatten

theorem y433RelP_eq {R : List ℕ} (hR : ∀ c ∈ R, c < 11) : y433RelP R = HS.pw (y433RelW R) := by
  unfold y433RelP y433RelW
  rw [fi_pw_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact y433P_eq (hR c (List.mem_reverse.1 hc))

@[expose, noinline] def y433Check (R : List ℕ) (w : List Native.Gen) (p : List Native.PGen) :
    Bool :=
  R.all (fun c => decide (c < 11)) && fiEqP (y433RelW R) w (y433RelP R) p

theorem wordLin_y433RelW_of_check
    {R : List ℕ} {w : List Native.Gen} {p : List Native.PGen}
    (h : y433Check R w p = true) (e : p = HS.pw w) : wordLin (y433RelW R) = wordLin w := by
  unfold y433Check at h
  rw [Bool.and_eq_true] at h
  have hR : ∀ c ∈ R, c < 11 := fun c hc => of_decide_eq_true (List.all_eq_true.1 h.1 c hc)
  exact wordLin_eq_of_fiEqP h.2 (y433RelP_eq hR) e

@[expose] def y433SpiderR : List ℕ := (List.replicate 10 [0, 1, 2, 0, 5, 6, 0, 8, 9]).flatten

@[expose] def y433F213R : List ℕ := (List.replicate 9 [0, 5, 6, 7, 1, 2, 8]).flatten

@[expose] def y433F312R : List ℕ := (List.replicate 9 [0, 8, 9, 10, 1, 2, 5]).flatten

@[expose, noinline] def y433SpiderCheck : Bool := y433Check y433SpiderR [] []

@[expose, noinline] def y433F213Check : Bool := y433Check y433F213R [] []

@[expose, noinline] def y433F312Check : Bool := y433Check y433F312R fiWBeta fiPBeta

theorem wordLin_y433Spider
    (h : y433SpiderCheck = true) : wordLin (y433RelW y433SpiderR) = 1 := by
  have := wordLin_y433RelW_of_check h (rfl : ([] : List Native.PGen) = HS.pw [])
  rwa [wordLin_nil] at this

theorem wordLin_y433F213
    (h : y433F213Check = true) : wordLin (y433RelW y433F213R) = 1 := by
  have := wordLin_y433RelW_of_check h (rfl : ([] : List Native.PGen) = HS.pw [])
  rwa [wordLin_nil] at this

theorem wordLin_y433F312
    (h : y433F312Check = true) :
    wordLin (y433RelW y433F312R) = wordLin fiWBeta :=
  wordLin_y433RelW_of_check h rfl

end CFSG.Monster.Existence
