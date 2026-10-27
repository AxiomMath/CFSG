module

public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HF166Inputs
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HF166Inputs

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def tStd : Array ℕ :=
  #[3, 1, 0, 2, 7, 5, 4, 6, 10, 8, 9, 11, 14, 12, 13, 15, 17, 19, 18, 16, 21, 23, 22, 20]

@[expose] def conj3AStd : List (Array ℕ) :=
  [
    #[1, 18, 9, 23, 16, 20, 8, 0, 14, 13, 4, 15, 21, 2, 10, 19, 11, 17, 22, 3, 12, 6, 7, 5],
    #[1, 22, 8, 19, 21, 17, 9, 0, 14, 12, 4, 15, 16, 3, 10, 23, 11, 20, 18, 2, 13, 7, 6, 5],
    #[8, 9, 22, 19, 20, 16, 5, 4, 12, 13, 23, 18, 17, 21, 1, 0, 11, 6, 15, 3, 14, 2, 7, 10],
    #[9, 8, 18, 23, 17, 21, 5, 4, 13, 12, 19, 22, 20, 16, 1, 0, 11, 7, 15, 2, 14, 3, 6, 10],
    #[10, 0, 8, 3, 23, 13, 12, 20, 5, 18, 16, 4, 9, 11, 2, 1, 7, 19, 6, 17, 22, 21, 15, 14],
    #[10, 0, 9, 2, 19, 12, 13, 17, 5, 22, 21, 4, 8, 11, 3, 1, 6, 23, 7, 20, 18, 16, 15, 14],
    #[10, 8, 4, 12, 19, 13, 7, 16, 1, 18, 23, 11, 14, 0, 6, 2, 15, 20, 5, 21, 22, 17, 3, 9],
    #[10, 9, 4, 13, 23, 12, 6, 21, 1, 22, 19, 11, 14, 0, 7, 3, 15, 17, 5, 16, 18, 20, 2, 8],
    #[12, 4, 21, 20, 16, 14, 6, 19, 18, 1, 22, 9, 7, 0, 13, 2, 8, 5, 10, 15, 11, 17, 3, 23],
    #[13, 4, 16, 17, 21, 14, 7, 23, 22, 1, 18, 8, 6, 0, 12, 3, 9, 5, 10, 15, 11, 20, 2, 19],
    #[14, 8, 10, 12, 11, 9, 13, 15, 18, 22, 16, 20, 4, 0, 6, 2, 23, 19, 21, 17, 1, 5, 3, 7],
    #[14, 9, 10, 13, 11, 8, 12, 15, 22, 18, 21, 17, 4, 0, 7, 3, 19, 23, 16, 20, 1, 5, 2, 6],
    #[19, 16, 9, 5, 20, 22, 8, 4, 12, 13, 6, 11, 1, 0, 10, 7, 15, 3, 18, 23, 14, 2, 21, 17],
    #[23, 21, 8, 5, 17, 18, 9, 4, 13, 12, 7, 11, 1, 0, 10, 6, 15, 2, 22, 19, 14, 3, 16, 20]]

@[expose] def fixCnt {T : PT 24} [Fact (T.check = true)] (mats : Array (List ℕ)) (p : T.Elem) : ℕ :=
  (fixMasks 11 (fun q m => actM (mats[q.idx]!) m) [p]).length

@[expose] def class3AHolds : Prop :=
  (∀ p : T24s3.Elem, p ≠ 1 → 16 ≤ fixCnt mats24s3 p →
      ∃ h ∈ conj3AStd, inAutOK h = true ∧ conjToB h (T24s3.arr p) tStd = true) ∧
  (∀ p : T24s5.Elem, p ≠ 1 → fixCnt mats24s5 p < 16) ∧
  (∀ p : T24s7.Elem, p ≠ 1 → fixCnt mats24s7 p < 16) ∧
  (∀ p : T24s11.Elem, p ≠ 1 → fixCnt mats24s11 p < 16) ∧
  (∀ p : T24s23.Elem, p ≠ 1 → fixCnt mats24s23 p < 16)

end CFSG.ASVolI.AppH.H157
