module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2Tab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin.H13.A6.GR

namespace G2

@[expose] def gmG2 : List (List ℕ) := [[1, 14, 16, 12, 5, 39], [1, 6, 4, 25, 17, 35]]

@[expose] def uG2 : ℕ := 34

@[expose] def wordsG2 : List (List ℕ) := [[], [0], [1], [0, 0], [1, 0], [0, 1]]

@[expose] def binvG2 : List ℕ := [54, 60, 15, 9, 46, 61]

theorem hBG2 : isOne 6 (mulC 6 (ccolsC 6 gmG2 wordsG2 uG2) binvG2) = true := by decide +kernel

theorem hwG2 : wordsG2.length = 6 := by decide

theorem cond_G2 : ∀ w < 2 ^ 6, condC 6 gmG2 wordsG2 binvG2 w = true → w = 54 ∨ w = 55 := by
  decide +kernel

theorem hs54 : ∀ cs ∈ bt 6 (fun pre c => okG2 pre c &&
    commOk1 6 (pcolsC 6 gmG2 wordsG2 binvG2 54) (pre ++ [c])) 6,
      leafF [] fullG2 6 cs = true := by
  decide +kernel

theorem hs55 : ∀ cs ∈ bt 6 (fun pre c => okG2 pre c &&
    commOk1 6 (pcolsC 6 gmG2 wordsG2 binvG2 55) (pre ++ [c])) 6,
      leafF [] fullG2 6 cs = true := by
  decide +kernel

theorem hsearchG2 : ∀ w < 2 ^ 6, condC 6 gmG2 wordsG2 binvG2 w = true →
    ∀ cs ∈ bt 6 (fun pre c => okG2 pre c &&
      commOk 6 (pcolsC 6 gmG2 wordsG2 binvG2 w) (pre ++ [c])) 6,
        leafC 6 [] fullG2 6 cs = true := by
  intro w hw hc cs hcs
  have hlen := length_of_mem_bt 6 6 cs hcs
  have hcs' : ∀ w', cs ∈ bt 6 (fun pre c => okG2 pre c &&
      commOk 6 (pcolsC 6 gmG2 wordsG2 binvG2 w') (pre ++ [c])) 6 →
      cs ∈ bt 6 (fun pre c => okG2 pre c &&
        commOk1 6 (pcolsC 6 gmG2 wordsG2 binvG2 w') (pre ++ [c])) 6 := fun w' h =>
    bt_mono 6 (fun pre c h => by
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, commOk1_of_commOk h.2⟩) 6 cs h
  rcases cond_G2 w hw hc with rfl | rfl
  · exact leafF_imp (by simp) hlen (hs54 cs (hcs' _ hcs))
  · exact leafF_imp (by simp) hlen (hs55 cs (hcs' _ hcs))

@[expose] def slistG2 : List (List ℕ) :=
  [
    [1, 2, 4, 8, 16, 32], [1, 14, 16, 12, 5, 39], [1, 6, 4, 25, 17, 35], [1, 10, 17, 25, 4, 58],
    [1, 6, 4, 24, 17, 39], [1, 18, 5, 28, 17, 56], [1, 27, 17, 29, 5, 32], [1, 26, 17, 28, 5, 36],
    [1, 30, 16, 8, 4, 40], [1, 2, 4, 9, 16, 36], [1, 27, 17, 28, 5, 49], [1, 31, 16, 9, 4, 45],
    [1, 19, 5, 28, 17, 45], [1, 30, 16, 9, 4, 56], [1, 11, 17, 25, 4, 46], [1, 23, 5, 12, 16, 43],
    [1, 23, 5, 13, 16, 46], [1, 15, 16, 13, 5, 35], [1, 22, 5, 13, 16, 58], [1, 7, 4, 25, 17, 55],
    [1, 11, 17, 24, 4, 63], [1, 14, 16, 13, 5, 55], [1, 10, 17, 24, 4, 43], [1, 15, 16, 12, 5, 51],
    [1, 22, 5, 12, 16, 63], [1, 7, 4, 24, 17, 51], [1, 3, 4, 8, 16, 53], [1, 31, 16, 8, 4, 61],
    [1, 18, 5, 29, 17, 61], [1, 26, 17, 29, 5, 53], [1, 19, 5, 29, 17, 40], [1, 3, 4, 9, 16, 49]]

@[expose] def gcolsG2 : List (List ℕ) :=
  [[1, 14, 16, 12, 5, 39], [1, 10, 17, 25, 4, 58],
    [1, 6, 4, 25, 17, 35], [1, 6, 4, 24, 17, 39]]

theorem slistG2_len : slistG2.all (fun c => c.length == 6) = true := by decide +kernel

theorem gcolsG2_len : ∀ p ∈ gcolsG2, p.length = 6 := by decide

theorem slistG2_one : ∃ c ∈ slistG2, normC 6 c = normC 6 (oneC 6) := by decide +kernel

theorem slistG2_cl_fast : slistG2.all (fun c => gcolsG2.all fun p =>
    slistG2.any fun c' => c' == mulL p c) = true := by decide +kernel

theorem slistG2_pow_fast : slistG2.all (fun c => isOneL (sqIterL c 3)) = true := by
  decide +kernel

end G2

end CFSG.Quasithin.H13.A6.GR
