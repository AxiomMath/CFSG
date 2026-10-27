module

public import CFSG.Quasithin.Vol2.Ch9L34M9

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.Mathieu

@[expose] def isInvN (n : ℕ) (cs : List ℕ) : Bool :=
  (List.range n).all fun i => actM cs (actM cs (2 ^ i)) == 2 ^ i

@[expose] def pickUnit (n r : ℕ) (cs : List ℕ) : List ℕ :=
  (List.range n).foldl (fun ws i =>
    if ws.length < r && decide (combos ((ws ++ [2 ^ i]).map fun w => actM cs w ^^^ w)).Nodup
    then ws ++ [2 ^ i] else ws) []

theorem chkIn9 : ((List.range 64).all fun p => p == 0 || !(isInvN 9 (cols9 p)) ||
    rankOK 4 9 (cols9 p) (pickUnit 9 4 (cols9 p))) = true := by
  decide +kernel

@[expose] def outW9 : List (ℕ × List ℕ) :=
  [(64, [1, 2, 4, 8, 32, 128]), (65, [1, 4, 8, 18, 32, 192]), (68, [1, 2, 8, 32, 68, 144]),
    (69, [1, 8, 18, 32, 68, 134]), (80, [1, 2, 8, 48, 128, 260]),
    (84, [1, 2, 8, 48, 144, 324]), (89, [1, 8, 18, 34, 192, 326]),
    (93, [1, 8, 18, 34, 194, 262])]

theorem chkOut9 : (outW9.all fun pw => decide (64 ≤ pw.1) && decide (pw.1 < 128) &&
    isInvN 9 (cols9 pw.1) && (pw.2.length == 6) &&
    pw.2.all (fun m => decide (m < 512) && (actM (cols9 pw.1) m == m)) &&
    decide (combos pw.2).Nodup) = true := by
  decide +kernel

theorem chkOutCover : ((List.range 64).all fun q => !(isInvN 9 (cols9 (q + 64))) ||
    outW9.any (fun pw => pw.1 == q + 64)) = true := by
  decide +kernel

end CFSG.Quasithin.H47W
