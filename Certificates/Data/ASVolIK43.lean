module

public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuCentInputs
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Monster.Code.Basis
public import Std.Data.HashSet
public meta import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public meta import CFSG.Quasithin.Background.HMathieuCentInputs
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Quasithin.Background.HMathieuBits
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.ASVolI.K43Data

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

@[expose] def gensK : List (Array ℕ) :=
  [#[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23],
    #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    #[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18],
    #[6, 2, 5, 0, 4, 1, 3, 7, 8, 9, 19, 18, 23, 22, 12, 13, 11, 10, 16, 17, 20, 21, 15, 14],
    #[1, 23, 6, 3, 22, 5, 14, 15, 20, 8, 7, 11, 12, 17, 2, 10, 16, 21, 18, 4, 9, 13, 19, 0],
    #[5, 7, 6, 4, 11, 10, 9, 8, 14, 13, 15, 12, 17, 19, 18, 16, 0, 3, 1, 2, 20, 21, 22, 23],
    #[12, 13, 20, 14, 5, 2, 19, 8, 3, 11, 16, 7, 10, 4, 17, 1, 18, 9, 6, 0, 15, 21, 22, 23],
    #[20, 3, 15, 18, 7, 17, 11, 19, 21, 16, 12, 0, 6, 2, 9, 1, 5, 13, 14, 10, 8, 4, 22, 23],
    #[4, 0, 22, 15, 6, 8, 17, 5, 1, 16, 3, 9, 19, 11, 20, 21, 10, 12, 13, 18, 2, 14, 7, 23]]

@[expose] def z0Arr : Array ℕ := #[21, 12, 9, 19, 10, 22, 16, 15, 8, 2, 4, 11, 1, 13, 14, 7, 6, 17, 18, 3, 20, 0, 5, 23]

@[expose] def octPts : List ℕ := [8, 11, 13, 14, 17, 18, 20, 23]

@[expose] def moGens : List (Array ℕ) :=
  [#[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    #[3, 4, 7, 0, 1, 6, 5, 2, 8, 15, 12, 11, 10, 13, 14, 9, 22, 17, 18, 21, 20, 19, 16, 23],
    #[6, 2, 1, 5, 7, 3, 0, 4, 8, 12, 15, 11, 9, 13, 14, 10, 21, 17, 18, 22, 20, 16, 19, 23],
    #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    #[7, 10, 9, 4, 15, 2, 1, 12, 8, 5, 6, 11, 0, 13, 14, 3, 19, 17, 20, 21, 23, 16, 22, 18],
    #[10, 19, 22, 12, 21, 9, 15, 16, 8, 5, 0, 11, 3, 13, 14, 6, 7, 17, 18, 1, 20, 4, 2, 23],
    #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18],
    #[21, 5, 0, 16, 3, 19, 22, 6, 8, 9, 15, 11, 10, 13, 14, 12, 4, 20, 17, 1, 18, 2, 7, 23],
    #[21, 12, 9, 19, 10, 22, 16, 15, 8, 2, 4, 11, 1, 13, 14, 7, 6, 17, 18, 3, 20, 0, 5, 23],
    #[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23]]

@[expose] def ptBase : List ℕ := [8, 11, 13, 14, 17, 18]

@[expose] def ptGens : List (List (Array ℕ)) :=
  [[#[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23], #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8], #[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8], #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18], #[6, 2, 5, 0, 4, 1, 3, 7, 8, 9, 19, 18, 23, 22, 12, 13, 11, 10, 16, 17, 20, 21, 15, 14], #[1, 23, 6, 3, 22, 5, 14, 15, 20, 8, 7, 11, 12, 17, 2, 10, 16, 21, 18, 4, 9, 13, 19, 0], #[5, 7, 6, 4, 11, 10, 9, 8, 14, 13, 15, 12, 17, 19, 18, 16, 0, 3, 1, 2, 20, 21, 22, 23], #[12, 13, 20, 14, 5, 2, 19, 8, 3, 11, 16, 7, 10, 4, 17, 1, 18, 9, 6, 0, 15, 21, 22, 23], #[20, 3, 15, 18, 7, 17, 11, 19, 21, 16, 12, 0, 6, 2, 9, 1, 5, 13, 14, 10, 8, 4, 22, 23], #[4, 0, 22, 15, 6, 8, 17, 5, 1, 16, 3, 9, 19, 11, 20, 21, 10, 12, 13, 18, 2, 14, 7, 23]],
   [#[6, 2, 5, 0, 4, 1, 3, 7, 8, 9, 19, 18, 23, 22, 12, 13, 11, 10, 16, 17, 20, 21, 15, 14], #[21, 10, 20, 15, 6, 19, 23, 3, 8, 4, 12, 5, 18, 22, 2, 7, 0, 9, 13, 1, 11, 14, 16, 17]],
   [#[13, 7, 9, 0, 17, 5, 6, 21, 8, 20, 19, 11, 4, 3, 14, 10, 16, 12, 23, 15, 2, 1, 18, 22], #[7, 14, 4, 1, 12, 0, 18, 16, 8, 13, 2, 11, 22, 17, 5, 9, 19, 10, 23, 6, 15, 20, 21, 3]],
   [#[10, 19, 5, 12, 18, 14, 9, 4, 8, 0, 22, 11, 1, 13, 15, 23, 16, 3, 20, 17, 21, 7, 6, 2], #[23, 19, 17, 22, 3, 15, 0, 12, 8, 7, 4, 11, 14, 13, 1, 2, 18, 16, 20, 21, 5, 9, 6, 10]],
   [#[21, 5, 0, 16, 3, 19, 22, 6, 8, 9, 15, 11, 10, 13, 14, 12, 4, 20, 17, 1, 18, 2, 7, 23], #[17, 19, 22, 23, 21, 18, 20, 16, 8, 7, 4, 11, 2, 13, 14, 1, 5, 10, 9, 6, 15, 0, 3, 12]],
   [#[7, 10, 9, 4, 15, 2, 1, 12, 8, 5, 6, 11, 0, 13, 14, 3, 19, 17, 20, 21, 23, 16, 22, 18], #[6, 2, 1, 5, 7, 3, 0, 4, 8, 12, 15, 11, 9, 13, 14, 10, 21, 17, 18, 22, 20, 16, 19, 23], #[10, 19, 22, 12, 21, 9, 15, 16, 8, 5, 0, 11, 3, 13, 14, 6, 7, 17, 18, 1, 20, 4, 2, 23]]]

@[expose] def vBase : List ℕ := [592, 648, 1378]

@[expose] def vGens : List (List (Array ℕ)) :=
  [[#[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23], #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8], #[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8], #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18], #[6, 2, 5, 0, 4, 1, 3, 7, 8, 9, 19, 18, 23, 22, 12, 13, 11, 10, 16, 17, 20, 21, 15, 14], #[1, 23, 6, 3, 22, 5, 14, 15, 20, 8, 7, 11, 12, 17, 2, 10, 16, 21, 18, 4, 9, 13, 19, 0], #[5, 7, 6, 4, 11, 10, 9, 8, 14, 13, 15, 12, 17, 19, 18, 16, 0, 3, 1, 2, 20, 21, 22, 23], #[12, 13, 20, 14, 5, 2, 19, 8, 3, 11, 16, 7, 10, 4, 17, 1, 18, 9, 6, 0, 15, 21, 22, 23], #[20, 3, 15, 18, 7, 17, 11, 19, 21, 16, 12, 0, 6, 2, 9, 1, 5, 13, 14, 10, 8, 4, 22, 23], #[4, 0, 22, 15, 6, 8, 17, 5, 1, 16, 3, 9, 19, 11, 20, 21, 10, 12, 13, 18, 2, 14, 7, 23]],
   [#[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8], #[1, 21, 9, 19, 4, 15, 6, 5, 18, 2, 10, 23, 0, 8, 17, 22, 16, 11, 20, 3, 13, 12, 7, 14], #[10, 19, 22, 0, 1, 6, 15, 2, 11, 5, 12, 8, 3, 18, 20, 9, 7, 23, 13, 21, 14, 4, 16, 17], #[1, 21, 2, 10, 3, 5, 16, 15, 18, 9, 19, 23, 0, 14, 17, 7, 6, 20, 11, 4, 13, 12, 22, 8], #[19, 12, 7, 11, 13, 15, 2, 22, 1, 5, 20, 4, 10, 23, 3, 9, 6, 8, 14, 18, 0, 21, 16, 17]],
   [#[10, 3, 5, 12, 0, 9, 15, 6, 18, 22, 21, 23, 19, 20, 17, 16, 7, 14, 8, 1, 13, 4, 2, 11], #[21, 12, 9, 3, 4, 5, 16, 7, 14, 2, 10, 20, 1, 23, 8, 15, 6, 18, 17, 19, 11, 0, 22, 13], #[0, 1, 9, 3, 4, 22, 16, 15, 11, 2, 10, 8, 12, 17, 20, 7, 6, 13, 23, 19, 14, 21, 5, 18], #[10, 19, 5, 1, 0, 9, 7, 16, 20, 22, 21, 14, 3, 18, 11, 6, 15, 23, 13, 12, 8, 4, 2, 17], #[20, 19, 2, 3, 14, 22, 16, 15, 21, 5, 18, 4, 1, 10, 13, 7, 6, 0, 11, 12, 8, 23, 9, 17], #[18, 1, 9, 19, 14, 22, 6, 16, 13, 5, 20, 17, 12, 11, 0, 15, 7, 8, 4, 3, 21, 23, 2, 10]]]

@[expose] def w5Basis : List ℕ := [3, 216, 297, 592, 1096]

@[expose] def sylConj : List (Array ℕ) :=
  [#[16, 0, 4, 3, 22, 1, 15, 9, 18, 10, 5, 8, 21, 11, 14, 2, 7, 23, 20, 19, 17, 6, 12, 13],
    #[4, 3, 9, 15, 22, 0, 16, 1, 8, 2, 5, 14, 19, 13, 20, 12, 6, 23, 17, 7, 11, 10, 21, 18]]

@[expose] def f3Wit : List (Array ℕ × Array ℕ) :=
  [(#[1, 0, 6, 4, 3, 7, 2, 5, 8, 16, 19, 11, 21, 13, 14, 22, 9, 17, 18, 10, 20, 12, 15, 23], #[0, 2, 3, 9, 21, 19, 7, 15, 23, 4, 12, 18, 6, 17, 14, 22, 5, 13, 20, 16, 11, 1, 10, 8]),
    (#[2, 6, 0, 7, 5, 4, 1, 3, 8, 21, 22, 11, 16, 13, 14, 19, 12, 17, 18, 15, 20, 9, 10, 23], #[0, 1, 3, 9, 16, 22, 4, 15, 17, 7, 12, 20, 6, 23, 13, 19, 5, 14, 18, 21, 8, 2, 10, 11]),
    (#[3, 4, 7, 0, 1, 6, 5, 2, 8, 15, 12, 11, 10, 13, 14, 9, 22, 17, 18, 21, 20, 19, 16, 23], #[0, 1, 2, 9, 16, 12, 6, 21, 18, 7, 22, 13, 4, 14, 20, 19, 5, 23, 17, 15, 11, 3, 10, 8]),
    (#[4, 3, 5, 1, 0, 2, 7, 6, 8, 22, 21, 11, 19, 13, 14, 16, 15, 17, 18, 12, 20, 10, 9, 23], #[0, 1, 2, 9, 16, 12, 6, 21, 23, 5, 15, 17, 3, 11, 8, 10, 7, 18, 13, 22, 14, 4, 19, 20]),
    (#[5, 7, 4, 6, 2, 0, 3, 1, 8, 10, 9, 11, 15, 13, 14, 12, 19, 17, 18, 16, 20, 22, 21, 23], #[0, 1, 2, 9, 16, 12, 6, 21, 14, 4, 19, 20, 7, 18, 13, 22, 3, 11, 8, 10, 23, 5, 15, 17]),
    (#[6, 2, 1, 5, 7, 3, 0, 4, 8, 12, 15, 11, 9, 13, 14, 10, 21, 17, 18, 22, 20, 16, 19, 23], #[0, 1, 3, 9, 16, 22, 4, 15, 14, 5, 21, 18, 2, 8, 11, 10, 7, 17, 20, 12, 23, 6, 19, 13]),
    (#[7, 5, 3, 2, 6, 1, 4, 0, 8, 19, 16, 11, 22, 13, 14, 21, 10, 17, 18, 9, 20, 15, 12, 23], #[0, 1, 2, 9, 16, 12, 6, 21, 11, 3, 10, 8, 5, 23, 17, 15, 4, 14, 20, 19, 18, 7, 22, 13]),
    (#[9, 16, 21, 15, 22, 10, 12, 19, 8, 0, 5, 11, 6, 13, 14, 3, 1, 17, 18, 7, 20, 2, 4, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15, 8, 9, 10, 11]),
    (#[10, 19, 22, 12, 21, 9, 15, 16, 8, 5, 0, 11, 3, 13, 14, 6, 7, 17, 18, 1, 20, 4, 2, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8]),
    (#[12, 21, 16, 10, 19, 15, 9, 22, 8, 6, 3, 11, 0, 13, 14, 5, 2, 17, 18, 4, 20, 1, 7, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 17, 16, 19, 18, 21, 20, 23, 22, 9, 8, 11, 10, 13, 12, 15, 14]),
    (#[15, 22, 19, 9, 16, 12, 10, 21, 8, 3, 6, 11, 5, 13, 14, 0, 4, 17, 18, 2, 20, 7, 1, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13]),
    (#[16, 9, 12, 22, 15, 19, 21, 10, 8, 1, 7, 11, 2, 13, 14, 4, 0, 17, 18, 5, 20, 6, 3, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18]),
    (#[19, 10, 15, 21, 12, 16, 22, 9, 8, 7, 1, 11, 4, 13, 14, 2, 5, 17, 18, 0, 20, 3, 6, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 12, 13, 10, 11, 8, 9, 22, 23, 20, 21, 18, 19, 16, 17]),
    (#[21, 12, 9, 19, 10, 22, 16, 15, 8, 2, 4, 11, 1, 13, 14, 7, 6, 17, 18, 3, 20, 0, 5, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]),
    (#[22, 15, 10, 16, 9, 21, 19, 12, 8, 4, 2, 11, 7, 13, 14, 1, 3, 17, 18, 6, 20, 5, 0, 23], #[0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20])]

@[expose] def classWit : List (Array ℕ × Array ℕ) :=
  [(#[0, 1, 2, 19, 10, 22, 6, 15, 14, 9, 4, 20, 12, 23, 8, 7, 16, 18, 17, 3, 11, 21, 5, 13], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]),
    (#[0, 1, 9, 3, 4, 22, 16, 15, 11, 2, 10, 8, 12, 17, 20, 7, 6, 13, 23, 19, 14, 21, 5, 18], #[0, 1, 3, 2, 6, 5, 4, 7, 17, 19, 16, 18, 12, 14, 13, 15, 10, 8, 11, 9, 23, 21, 22, 20]),
    (#[0, 1, 9, 19, 10, 5, 16, 7, 20, 2, 4, 14, 12, 18, 11, 15, 6, 23, 13, 3, 8, 21, 22, 17], #[0, 1, 5, 2, 6, 3, 7, 4, 8, 22, 16, 14, 12, 18, 20, 10, 15, 17, 23, 9, 11, 21, 19, 13]),
    (#[0, 12, 2, 3, 10, 22, 16, 7, 23, 9, 4, 18, 1, 14, 13, 15, 6, 20, 11, 19, 17, 21, 5, 8], #[0, 2, 3, 1, 6, 5, 7, 4, 18, 19, 16, 17, 9, 8, 11, 10, 15, 14, 13, 12, 20, 21, 22, 23]),
    (#[0, 12, 2, 19, 4, 5, 16, 15, 13, 9, 10, 17, 1, 8, 23, 7, 6, 11, 20, 3, 18, 21, 22, 14], #[0, 2, 4, 1, 6, 7, 5, 3, 23, 10, 16, 13, 9, 20, 14, 19, 22, 11, 17, 12, 8, 21, 15, 18]),
    (#[0, 12, 9, 3, 10, 5, 6, 15, 18, 2, 4, 23, 1, 20, 17, 7, 16, 14, 8, 19, 13, 21, 22, 11], #[0, 3, 5, 1, 4, 2, 6, 7, 13, 22, 10, 17, 19, 8, 20, 15, 16, 11, 23, 12, 14, 21, 9, 18]),
    (#[0, 12, 9, 19, 4, 22, 6, 7, 17, 2, 10, 13, 1, 11, 18, 15, 16, 8, 14, 3, 23, 21, 5, 20], #[0, 4, 6, 1, 3, 5, 7, 2, 8, 16, 19, 11, 10, 18, 17, 9, 15, 23, 20, 12, 13, 21, 22, 14]),
    (#[21, 1, 2, 3, 10, 5, 16, 15, 17, 9, 4, 13, 12, 11, 18, 7, 6, 8, 14, 19, 23, 0, 22, 20], #[0, 4, 6, 1, 3, 5, 7, 2, 8, 16, 19, 11, 10, 18, 17, 9, 15, 23, 20, 12, 13, 21, 22, 14]),
    (#[21, 1, 2, 19, 4, 22, 16, 7, 18, 9, 10, 23, 12, 20, 17, 15, 6, 14, 8, 3, 13, 0, 5, 11], #[0, 3, 5, 1, 4, 2, 6, 7, 13, 22, 10, 17, 19, 8, 20, 15, 16, 11, 23, 12, 14, 21, 9, 18]),
    (#[21, 1, 9, 3, 10, 22, 6, 7, 13, 2, 4, 17, 12, 8, 23, 15, 16, 11, 20, 19, 18, 0, 5, 14], #[0, 2, 4, 1, 6, 7, 5, 3, 23, 10, 16, 13, 9, 20, 14, 19, 22, 11, 17, 12, 8, 21, 15, 18]),
    (#[21, 1, 9, 19, 4, 5, 6, 15, 23, 2, 10, 18, 12, 14, 13, 7, 16, 20, 11, 3, 17, 0, 22, 8], #[0, 2, 3, 1, 6, 5, 7, 4, 18, 19, 16, 17, 9, 8, 11, 10, 15, 14, 13, 12, 20, 21, 22, 23]),
    (#[21, 12, 2, 3, 4, 22, 6, 15, 20, 9, 10, 14, 1, 18, 11, 7, 16, 23, 13, 19, 8, 0, 5, 17], #[0, 1, 5, 2, 6, 3, 7, 4, 8, 22, 16, 14, 12, 18, 20, 10, 15, 17, 23, 9, 11, 21, 19, 13]),
    (#[21, 12, 2, 19, 10, 5, 6, 7, 11, 9, 4, 8, 1, 17, 20, 15, 16, 13, 23, 3, 14, 0, 22, 18], #[0, 1, 3, 2, 6, 5, 4, 7, 17, 19, 16, 18, 12, 14, 13, 15, 10, 8, 11, 9, 23, 21, 22, 20]),
    (#[21, 12, 9, 3, 4, 5, 16, 7, 14, 2, 10, 20, 1, 23, 8, 15, 6, 18, 17, 19, 11, 0, 22, 13], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])]

@[expose] def arrMul (a b : Array ℕ) : Array ℕ := Array.ofFn (n := 24) fun i => a[b[i.1]!]!

@[expose] def arrConj (g a : Array ℕ) : Array ℕ := arrMul (arrMul g a) (invArr g)

@[expose] def idArr : Array ℕ := Array.ofFn (n := 24) fun i => i.1

@[expose] def tArr (p : ℕ) : Array ℕ := T24s2.elems[p]!

@[expose] def z0Idx : ℕ := (T24s2.elems.findIdx? (· == z0Arr)).getD 0

@[expose] def e0mask : ℕ := octPts.foldl (fun acc i => acc ||| (1 <<< i)) 0

@[expose] def fixesOct (a : Array ℕ) : Bool := octPts.all fun i => a[i]! == i

@[expose] def bfsTable (step : ℕ → ℕ → ℕ) (ngen x0 cap : ℕ) : Array (ℕ × ℕ × ℕ) := Id.run do
  let mut seen : Std.HashSet ℕ := (∅ : Std.HashSet ℕ).insert x0
  let mut tab : Array (ℕ × ℕ × ℕ) := #[(x0, 0, 0)]
  for h in [0:cap] do
    if h < tab.size then
      let y := tab[h]!.1
      for g in [0:ngen] do
        let z := step g y
        if !seen.contains z then
          seen := seen.insert z
          tab := tab.push (z, h, g)
    else break
  return tab

@[expose] def derivOK (step : ℕ → ℕ → ℕ) (ngen x0 : ℕ) (tab : Array (ℕ × ℕ × ℕ)) : Bool :=
  decide (0 < tab.size) && tab[0]!.1 == x0 &&
    (List.range tab.size).all fun i =>
      i == 0 || (decide (tab[i]!.2.1 < i) && decide (tab[i]!.2.2 < ngen) &&
        tab[i]!.1 == step tab[i]!.2.2 tab[tab[i]!.2.1]!.1)

@[expose] def tabNodupLt (bound : ℕ) (tab : Array (ℕ × ℕ × ℕ)) : Bool :=
  decide ((tab.toList.map (·.1)).Nodup) && tab.all fun e => decide (e.1 < bound)

@[expose] def gStep (gens : List (Array ℕ)) (act : Array ℕ → ℕ → ℕ) (g y : ℕ) : ℕ :=
  act (gens[g]!) y

@[expose] def octTab (_ : Unit := ()) : Array (ℕ × ℕ × ℕ) :=
  bfsTable (gStep gensK permM) gensK.length e0mask 100000

@[expose] def octMiss (tab : Array (ℕ × ℕ × ℕ)) : ℕ :=
  treeSumN (fun a => if popc 24 a == 8 && !(tab.any (·.1 == a)) then 1 else 0) Bmask 12 0

@[expose] def octOK (_ : Unit := ()) : Bool :=
  let tab := octTab ()
  gensK.all inAutOK && octPts.all (· < 24) && octPts.Nodup && octPts.length == 8 &&
    derivOK (gStep gensK permM) gensK.length e0mask tab && octMiss tab == 0

@[expose] def ptTab (i : ℕ) : Array (ℕ × ℕ × ℕ) :=
  bfsTable (fun g y => ((ptGens[i]!)[g]!)[y]!) (ptGens[i]!).length ptBase[i]! 1000

@[expose] def ptChainOK (_ : Unit := ()) : Bool :=
  ptBase.length == 6 && ptGens.length == 6 && ptBase.all (· < 24) &&
  (List.range 6).all fun i =>
    (ptGens[i]!).all (fun g => inAutOK g && (ptBase.take i).all fun b => g[b]! == b) &&
    derivOK (fun g y => ((ptGens[i]!)[g]!)[y]!) (ptGens[i]!).length ptBase[i]! (ptTab i) &&
    tabNodupLt 24 (ptTab i) &&
    (ptTab i).size == [24, 23, 22, 21, 20, 3][i]!

@[expose] def vecTab (i : ℕ) : Array (ℕ × ℕ × ℕ) :=
  bfsTable (gStep (vGens[i]!) actC11) (vGens[i]!).length vBase[i]! 5000

@[expose] def vecChainOK (_ : Unit := ()) : Bool :=
  vBase.length == 3 && vGens.length == 3 && vBase.all (· < 2048) &&
  (List.range 3).all fun i =>
    (vGens[i]!).all (fun g => inAutOK g && (vBase.take i).all fun b => actC11 g b == b) &&
    derivOK (gStep (vGens[i]!) actC11) (vGens[i]!).length vBase[i]! (vecTab i) &&
    tabNodupLt 2048 (vecTab i) &&
    (vecTab i).size == [759, 280, 72][i]!

@[expose] def w5Masks (_ : Unit := ()) : List ℕ := combos w5Basis

@[expose] def vzMasks (_ : Unit := ()) : List ℕ :=
  (w5Masks ()).filter fun m => actC11 z0Arr m == m

@[expose] def kIdx (_ : Unit := ()) : List ℕ :=
  (List.range T24s2.n).filter fun p => fixesOct (tArr p)

@[expose] def dzIdx (_ : Unit := ()) : List ℕ :=
  let vz := vzMasks ()
  (List.range T24s2.n).filter fun p => vz.all fun m => actC11 (tArr p) m == m

@[expose] def listsOK (_ : Unit := ()) : Bool :=
  let ks := kIdx ()
  let ds := dzIdx ()
  decide (z0Idx < T24s2.n) && tArr z0Idx == z0Arr &&
  (List.range T24s2.n).all (fun p => T24s2.mulIdx p z0Idx == T24s2.mulIdx z0Idx p) &&
  ks.length == 16 && ds.length == 16 && (w5Masks ()).length == 32 && (vzMasks ()).length == 16 &&
  (combos w5Basis).Nodup &&
  arrMul z0Arr z0Arr == idArr && (List.range 24).any (fun i => z0Arr[i]! != i) &&
  ks.all (fun p => arrMul (tArr p) z0Arr == arrMul z0Arr (tArr p)) &&
  ds.all (fun p => arrMul (tArr p) z0Arr == arrMul z0Arr (tArr p)) &&
  ds.all (fun p => ds.all fun q => arrMul (tArr p) (tArr q) == arrMul (tArr q) (tArr p)) &&
  ds.all (fun p => arrMul (tArr p) (tArr p) == idArr) &&
  (List.range T24s2.n).all (fun p => (tArr p).size == 24) &&
  ds.all (fun p => fixesOct (tArr p) == (tArr p == idArr || tArr p == z0Arr)) &&
  vBase.all (vzMasks ()).contains &&
  fixesOct z0Arr && (List.range 24).all fun j => (z0Arr[j]! == j) == octPts.contains j

@[expose] def f3OK (_ : Unit := ()) : Bool :=
  let ks := kIdx ()
  f3Wit.all (fun kg => inAutOK kg.2 && permM kg.2 e0mask == e0mask && arrConj kg.2 z0Arr == kg.1) &&
  ks.all (fun p => tArr p == idArr || f3Wit.any (fun kg => kg.1 == tArr p))

@[expose] def applyWord (gens : List (Array ℕ)) (w : List ℕ) (m : ℕ) : ℕ :=
  w.foldr (fun g acc => actC11 (gens[g]!) acc) m

@[expose] def wordsOfLen : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, n => (wordsOfLen k n).flatMap fun w => (List.range n).map (· :: w)

@[expose] def wordPool (n L : ℕ) : List (List ℕ) := (List.range (L + 1)).flatMap fun k => wordsOfLen k n

@[expose] def pick6 (cands : List ℕ) : List ℕ :=
  cands.foldl (fun acc x => if acc.length < 6 && !(combos acc).contains x then x :: acc else acc) []

@[expose] def indep6 (cands : List ℕ) : Bool :=
  let bs := pick6 cands
  bs.length == 6 && decide ((combos bs).Nodup) && bs.all cands.contains

@[expose] def f4OK (_ : Unit := ()) : Bool :=
  let w5 := w5Masks ()
  let pool := wordPool moGens.length 2
  moGens.all (fun g => inAutOK g && permM g e0mask == e0mask) &&
  (List.range 2048).all fun m =>
    w5.contains m || indep6 (pool.map fun w => applyWord moGens w m)

@[expose] def sylOK (_ : Unit := ()) : Bool :=
  let ks := (kIdx ()).map tArr
  let ds := (dzIdx ()).map tArr
  sylConj.all (fun c => inAutOK c && arrMul c z0Arr == arrMul z0Arr c) &&
  (List.range T24s2.n).all fun p =>
    !(sylConj.all fun c => T24s2.elems.contains (arrMul (arrMul (invArr c) (tArr p)) c)) ||
      ks.any (fun k => ds.any fun d => arrMul k d == tArr p)

@[expose] def quadPair (a b : Array ℕ) : Bool :=
  (List.range 2048).all fun m =>
    let w := actC11 b m ^^^ m
    actC11 a w == w

@[expose] def classOK (_ : Unit := ()) : Bool :=
  let ds := dzIdx ()
  let xs := ds.filter fun p => tArr p != idArr && tArr p != z0Arr
  xs.length == 14 &&
  (List.range T24s2.n).all (fun p =>
    let a := tArr p
    !(arrMul a a == idArr && a != idArr && a != z0Arr && quadPair z0Arr a) || ds.contains p) &&
  classWit.all (fun xg =>
    inAutOK xg.1 && inAutOK xg.2 && arrMul xg.2 z0Arr == arrMul z0Arr xg.2 &&
      (arrConj xg.2 (classWit[0]!).1 == xg.1 || arrConj xg.2 (classWit[0]!).1 == arrMul xg.1 z0Arr)) &&
  xs.all (fun p => classWit.any (·.1 == tArr p))

@[expose] def dmasks (a : Array ℕ) : List ℕ := (List.range 11).map fun j => actC11 a (2 ^ j) ^^^ 2 ^ j

@[expose] def modOKx (ax : Array ℕ) (dz : List (Array ℕ)) : Bool :=
  let az := z0Arr
  let axz := arrMul ax az
  let dxm := dmasks ax
  let dzm := dmasks az
  let vz := vzMasks ()
  let stab := dz.filter fun p => (List.range 2048).all fun m =>
    let w := actC11 ax m ^^^ m
    actC11 p w == w
  let four := [idArr, ax, az, axz]
  stab.all four.contains && four.all stab.contains &&
  ((List.range 2048).filter fun m => actC11 ax m == m && actC11 az m == m).length == 64 &&
  (List.range 2048).all (fun m => [ax, az, axz].all fun y =>
    let w := actC11 y m ^^^ m
    actC11 ax w == w && actC11 az w == w) &&
  indep6 (dxm ++ dzm) && indep6 (vz ++ dxm)

@[expose] def modOK (_ : Unit := ()) : Bool :=
  let vz := vzMasks ()
  let dzm := dmasks z0Arr
  let dz := (dzIdx ()).map tArr
  vz.all (combos dzm).contains &&
  (List.range 2048).all (fun m => vz.contains (actC11 z0Arr m ^^^ m)) &&
  dz.all fun ax => ax == idArr || ax == z0Arr || modOKx ax dz

end CFSG.ASVolI.K43Data
