module

public import CFSG.Quasithin.AppendixH.H14.H142Table

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu

@[expose] def hTabArr : Array (Array ℕ) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[1, 0, 6, 4, 3, 7, 2, 5, 8, 16, 19, 11, 21, 13, 14, 22, 9, 17, 18, 10, 20, 12, 15, 23],
    #[2, 6, 0, 7, 5, 4, 1, 3, 8, 21, 22, 11, 16, 13, 14, 19, 12, 17, 18, 15, 20, 9, 10, 23],
    #[6, 2, 1, 5, 7, 3, 0, 4, 8, 12, 15, 11, 9, 13, 14, 10, 21, 17, 18, 22, 20, 16, 19, 23],
    #[3, 4, 7, 0, 1, 6, 5, 2, 8, 15, 12, 11, 10, 13, 14, 9, 22, 17, 18, 21, 20, 19, 16, 23],
    #[4, 3, 5, 1, 0, 2, 7, 6, 8, 22, 21, 11, 19, 13, 14, 16, 15, 17, 18, 12, 20, 10, 9, 23],
    #[7, 5, 3, 2, 6, 1, 4, 0, 8, 19, 16, 11, 22, 13, 14, 21, 10, 17, 18, 9, 20, 15, 12, 23],
    #[5, 7, 4, 6, 2, 0, 3, 1, 8, 10, 9, 11, 15, 13, 14, 12, 19, 17, 18, 16, 20, 22, 21, 23],
    #[9, 16, 21, 15, 22, 10, 12, 19, 8, 0, 5, 11, 6, 13, 14, 3, 1, 17, 18, 7, 20, 2, 4, 23],
    #[16, 9, 12, 22, 15, 19, 21, 10, 8, 1, 7, 11, 2, 13, 14, 4, 0, 17, 18, 5, 20, 6, 3, 23],
    #[21, 12, 9, 19, 10, 22, 16, 15, 8, 2, 4, 11, 1, 13, 14, 7, 6, 17, 18, 3, 20, 0, 5, 23],
    #[12, 21, 16, 10, 19, 15, 9, 22, 8, 6, 3, 11, 0, 13, 14, 5, 2, 17, 18, 4, 20, 1, 7, 23],
    #[15, 22, 19, 9, 16, 12, 10, 21, 8, 3, 6, 11, 5, 13, 14, 0, 4, 17, 18, 2, 20, 7, 1, 23],
    #[22, 15, 10, 16, 9, 21, 19, 12, 8, 4, 2, 11, 7, 13, 14, 1, 3, 17, 18, 6, 20, 5, 0, 23],
    #[19, 10, 15, 21, 12, 16, 22, 9, 8, 7, 1, 11, 4, 13, 14, 2, 5, 17, 18, 0, 20, 3, 6, 23],
    #[10, 19, 22, 12, 21, 9, 15, 16, 8, 5, 0, 11, 3, 13, 14, 6, 7, 17, 18, 1, 20, 4, 2, 23]]

@[expose] def hGens : List (Array ℕ) :=
  [#[0, 1, 3, 12, 21, 19, 4, 10, 8, 22, 6, 18, 9, 17, 20, 7, 15, 14, 13, 2, 23, 16, 5, 11],
    #[0, 2, 6, 10, 22, 19, 1, 15, 8, 4, 12, 14, 3, 13, 18, 21, 5, 17, 11, 16, 20, 7, 9, 23]]

@[expose] def hVbfs : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 0), (2, 1, 0), (4, 0, 1), (3, 1, 1), (11, 0, 2), (15, 1, 2), (5, 0, 3), (8, 0, 4),
      (10, 0, 6), (13, 1, 6), (9, 0, 8), (6, 1, 8), (7, 0, 9), (12, 0, 10), (14, 0, 12)]

@[expose] def hPts : List ℕ := [11, 13, 14, 17, 18, 20, 23]

@[expose] def iterArr (a : Array ℕ) (j x : ℕ) : ℕ := (fun y => a[y]!)^[j] x

theorem hTab_ok : tabOK hTabArr = true := by decide +kernel

theorem hTab_fix : ∀ n < 16, (hTabArr[n]!)[8]! = 8 ∧ ∀ i ∈ hPts, (hTabArr[n]!)[i]! = i := by
  decide +kernel

theorem hTab_mask : ∀ n < 16, permM hTabArr[n]! 9857280 = 9857280 := by decide +kernel

theorem hGens_ok : ∀ a ∈ hGens, inAutOK a = true ∧ a[8]! = 8 ∧ permM a 9857280 = 9857280 := by
  decide +kernel

theorem hVbfs_ok : vbfsOK hTabArr hGens 1 hVbfs = true := by decide +kernel

theorem hVbfs_cover : ∀ n < 16, 0 < n → ∃ e ∈ hVbfs, e.1 = n := by decide +kernel

theorem hGens_noncomm : cmap hTabArr hGens[0]! 2 < 16 ∧ cmap hTabArr hGens[0]! 2 ≠ 2 := by
  decide +kernel

theorem hGens_cycle : ∀ y ∈ hPts, ∃ j < 7, iterArr hGens[0]! j 11 = y := by decide +kernel

theorem hGens_three : (hGens[1]!)[11]! = 14 ∧ (hGens[1]!)[14]! = 18 ∧ (hGens[1]!)[18]! = 11 ∧
    (hGens[1]!)[13]! = 13 ∧ (hGens[1]!)[17]! = 17 ∧ (hGens[1]!)[20]! = 20 ∧ (hGens[1]!)[23]! = 23 := by
  decide +kernel

end CFSG.Quasithin.AppendixH.H14
