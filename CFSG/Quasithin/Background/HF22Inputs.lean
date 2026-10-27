
module

public import CFSG.Quasithin.Background.HF166Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public meta import CFSG.Quasithin.Background.HF166Inputs
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Monster.Code.Basis
public meta import CFSG.Quasithin.Background.HMathieuSyl22Inputs

public section

namespace CFSG.Quasithin.H.Mathieu

@[expose] def s0Arr22 : Array ℕ :=
  #[0, 1, 2, 17, 13, 6, 20, 8, 12, 11, 4, 22, 7, 10, 21, 14, 16, 18, 3, 19, 5, 15, 9, 23]

@[expose] def conj3A22 : List (Array ℕ) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[0, 1, 9, 6, 15, 7, 8, 14, 13, 19, 3, 23, 17, 4, 18, 10, 22, 5, 20, 11, 12, 21, 2, 16],
    #[0, 1, 11, 5, 14, 4, 10, 15, 12, 16, 3, 23, 18, 7, 17, 8, 22, 6, 20, 9, 13, 21, 2, 19],
    #[0, 1, 20, 9, 14, 2, 19, 4, 12, 3, 7, 17, 15, 13, 10, 21, 5, 22, 11, 6, 16, 8, 18, 23],
    #[0, 1, 23, 14, 13, 5, 20, 7, 12, 9, 10, 22, 8, 4, 3, 17, 16, 15, 21, 19, 6, 18, 11, 2],
    #[1, 0, 7, 23, 14, 5, 20, 13, 21, 9, 4, 11, 3, 18, 15, 10, 12, 19, 2, 8, 6, 17, 22, 16],
    #[1, 0, 8, 23, 10, 5, 6, 21, 13, 22, 15, 11, 3, 17, 4, 14, 12, 2, 19, 7, 20, 18, 9, 16],
    #[1, 0, 22, 6, 15, 2, 19, 10, 12, 3, 8, 18, 14, 13, 4, 21, 11, 20, 5, 9, 16, 7, 17, 23]]

@[expose] def codeFixArr10 (a : Array ℕ) : List ℕ :=
  (List.range (2 ^ 10)).filter fun m => actC10 a m == m

@[expose] def h1607Check22 : Prop :=
  ∀ s : T22s3.Elem, (codeFixArr10 (T22s3.arr s)).length = 2 ^ 4 →
    ∃ h ∈ conj3A22, inAutOK h = true ∧
      ((h[0]! == 0 && h[1]! == 1) || (h[0]! == 1 && h[1]! == 0)) = true ∧
      conjToB h (T22s3.arr s) s0Arr22 = true

end CFSG.Quasithin.H.Mathieu
