
module

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuCentInputs
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuAvoid
public meta import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuAvoid
public meta import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Monster.Code.Basis
public meta import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuCentInputs

public section

namespace CFSG.Quasithin.H.Mathieu

@[expose] def s0Arr : Array ℕ :=
  #[0, 1, 6, 5, 17, 12, 14, 19, 9, 20, 22, 11, 3, 7, 2, 4, 16, 15, 18, 13, 8, 10, 21, 23]

@[expose] def conj3A24 : List (Array ℕ) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    #[4, 15, 23, 20, 22, 8, 18, 3, 7, 13, 10, 11, 9, 21, 16, 2, 1, 12, 0, 6, 19, 14, 5, 17],
    #[8, 9, 1, 19, 4, 7, 18, 3, 22, 21, 17, 0, 13, 15, 16, 2, 11, 5, 23, 14, 10, 6, 12, 20],
    #[10, 2, 21, 6, 17, 8, 9, 15, 18, 0, 13, 3, 22, 23, 14, 16, 5, 19, 12, 7, 1, 4, 11, 20],
    #[10, 2, 22, 14, 19, 9, 8, 7, 18, 1, 4, 3, 21, 23, 6, 16, 12, 17, 5, 15, 0, 13, 11, 20],
    #[10, 8, 20, 22, 11, 9, 21, 23, 0, 1, 7, 4, 3, 2, 5, 6, 17, 19, 15, 13, 16, 18, 14, 12],
    #[10, 21, 3, 9, 19, 8, 5, 13, 16, 0, 17, 23, 20, 2, 12, 14, 11, 15, 18, 4, 1, 7, 6, 22],
    #[10, 21, 4, 18, 9, 11, 15, 3, 13, 7, 5, 1, 16, 2, 17, 12, 0, 14, 23, 20, 19, 6, 8, 22],
    #[10, 22, 3, 8, 17, 9, 12, 4, 16, 1, 19, 23, 20, 2, 5, 6, 11, 7, 18, 13, 0, 15, 14, 21],
    #[13, 3, 8, 9, 21, 19, 5, 10, 23, 16, 11, 4, 12, 2, 7, 6, 15, 18, 17, 0, 1, 22, 14, 20],
    #[16, 23, 4, 20, 21, 9, 15, 2, 19, 7, 3, 0, 8, 6, 17, 10, 1, 22, 11, 14, 13, 5, 12, 18],
    #[17, 15, 8, 18, 13, 0, 9, 3, 21, 22, 12, 11, 16, 2, 20, 5, 23, 6, 1, 19, 10, 14, 7, 4],
    #[19, 4, 17, 7, 1, 15, 13, 0, 11, 23, 8, 22, 3, 2, 12, 14, 10, 20, 21, 9, 16, 18, 6, 5],
    #[21, 3, 7, 13, 15, 10, 12, 17, 1, 16, 0, 8, 5, 2, 22, 14, 9, 18, 20, 23, 11, 4, 6, 19]]

@[expose] def conjToB (h a b : Array ℕ) : Bool :=
  (List.range 24).all fun i => h[a[i]!]! == b[h[i]!]!

@[expose] def codeFixArr (a : Array ℕ) : List ℕ :=
  (List.range (2 ^ 11)).filter fun m => actC11 a m == m

@[expose] def h166Check : Prop :=
  ∀ s : T24s3.Elem, (codeFixArr (T24s3.arr s)).length = 2 ^ 5 →
    ∃ h ∈ conj3A24, inAutOK h = true ∧ conjToB h (T24s3.arr s) s0Arr = true

end CFSG.Quasithin.H.Mathieu
