module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ASVolI

@[expose] def burnsideF48t_u52eF : Array ℕ :=
  #[0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 18, 17, 22, 24, 23, 19, 21, 20,
  35, 36, 38, 37, 42, 44, 43, 39, 41, 40, 25, 26, 28, 27, 32, 34, 33, 29, 31, 30, 45, 47, 46,
  48, 50, 49, 51, 52, 54, 53, 58, 60, 59, 55, 57, 56, 71, 72, 74, 73, 78, 80, 79, 75, 77, 76,
  61, 62, 64, 63, 68, 70, 69, 65, 67, 66, 81, 82, 84, 83, 88, 90, 89, 85, 87, 86, 91, 93, 92,
  94, 96, 95, 103, 105, 104, 106, 108, 107, 97, 99, 98, 100, 102, 101, 137, 138, 140, 139, 144,
  146, 145, 141, 143, 142, 147, 149, 148, 150, 152, 151, 159, 161, 160, 162, 164, 163, 153, 155,
  154, 156, 158, 157, 109, 110, 112, 111, 116, 118, 117, 113, 115, 114, 119, 121, 120, 122, 124,
  123, 131, 133, 132, 134, 136, 135, 125, 127, 126, 128, 130, 129, 165, 167, 166, 168, 170, 169,
  171, 173, 172, 183, 185, 184, 186, 188, 187, 189, 191, 190, 174, 176, 175, 177, 179, 178, 180,
  182, 181, 192, 194, 193, 195, 197, 196, 198, 200, 199, 210, 212, 211, 213, 215, 214, 216, 218,
  217, 201, 203, 202, 204, 206, 205, 207, 209, 208, 219, 221, 220, 222, 224, 223, 225, 227, 226,
  237, 239, 238, 240, 242, 241, 243, 245, 244, 228, 230, 229, 231, 233, 232, 234, 236, 235, 246,
  248, 247, 249, 251, 250, 258, 260, 259, 261, 263, 262, 252, 254, 253, 255, 257, 256, 264, 266,
  265, 267, 269, 268, 276, 278, 277, 279, 281, 280, 270, 272, 271, 273, 275, 274, 282, 284, 283,
  285, 287, 286, 289, 288, 292, 293, 290, 291, 301, 300, 304, 305, 302, 303, 295, 294, 298, 299,
  296, 297, 324, 325, 328, 329, 327, 326, 336, 337, 340, 341, 339, 338, 330, 331, 334, 335, 333,
  332, 306, 307, 311, 310, 308, 309, 318, 319, 323, 322, 320, 321, 312, 313, 317, 316, 314, 315,
  402, 404, 403, 405, 407, 406, 408, 409, 413, 412, 410, 411, 420, 421, 425, 424, 422, 423, 414,
  415, 419, 418, 416, 417, 445, 444, 448, 449, 446, 447, 457, 456, 460, 461, 458, 459, 451, 450,
  454, 455, 452, 453, 426, 427, 430, 431, 429, 428, 438, 439, 442, 443, 441, 440, 432, 433, 436,
  437, 435, 434, 342, 344, 343, 345, 347, 346, 348, 349, 352, 353, 351, 350, 360, 361, 364, 365,
  363, 362, 354, 355, 358, 359, 357, 356, 384, 385, 389, 388, 386, 387, 396, 397, 401, 400, 398,
  399, 390, 391, 395, 394, 392, 393, 367, 366, 370, 371, 368, 369, 379, 378, 382, 383, 380, 381,
  373, 372, 376, 377, 374, 375]

@[expose] def burnsideF48t_u52eKhW : List (List (List (Fin 5 × Bool))) :=
  [
    [
      [],
      [(1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (0, true), (1, false)],
      [(1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, true), (1, true)],
      [(1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
      [(0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true),
      (1, true), (0, true)],
      [(1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (0, true), (1, true)],
      [(0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (0, false), (0,
      false), (1, false), (0, false)],
      [(4, false)],
      [(4, false), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1,
      true), (0, true), (0, true), (1, false)],
      [(4, false), (1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0,
      false), (1, false), (0, true), (1, true)],
      [(4, false), (1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
      [(4, false), (0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false),
      (1, true), (1, true), (0, true)],
      [(4, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0,
      false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(4, false), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false)],
      [(4, false), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, true)],
      [(4, false), (0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (0,
      false), (0, false), (1, false), (0, false)]],
    [
      [],
      [(1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (0, true), (1, false)],
      [(1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, true), (1, true)],
      [(1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
      [(0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true),
      (1, true), (0, true)],
      [(1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (0, true), (1, true)],
      [(0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (0, false), (0,
      false), (1, false), (0, false)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, false), (0,
      false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1,
      false)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, true), (0,
      false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
      (1, true)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, true), (0,
      false), (1, true), (0, true), (0, true), (1, true)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (0, true), (1,
      true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (1, true), (0,
      true)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, false), (0,
      false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0,
      false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, false), (0,
      false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (1, true), (0,
      false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0,
      true), (1, true), (0, true), (0, true), (1, true)],
      [(1, false), (0, true), (4, true), (0, false), (1, false), (0, false), (0, false), (1,
      false), (1, false), (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
      (0, false)]],
    [
      [],
      [(1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (0, true), (1, false)],
      [(1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, true), (1, true)],
      [(1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
      [(0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true),
      (1, true), (0, true)],
      [(1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (0, true), (1, true)],
      [(0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (0, false), (0,
      false), (1, false), (0, false)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0,
      true), (1, true), (0, true), (0, true), (1, false)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false), (0, false),
      (1, false), (0, false), (1, false), (0, true), (1, true)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (0, true), (1,
      true)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1,
      true), (0, false), (1, true), (1, true), (0, true)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
      (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0,
      true), (1, false)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true),
      (1, false)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0,
      true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1,
      true)],
      [(0, true), (1, true), (1, true), (0, true), (4, false), (0, false), (0, false), (1,
      true), (1, true), (0, true), (0, false), (1, false), (1, false), (0, true), (1, false),
      (0, false), (0, false), (0, false), (1, false), (0, false)]],
    [
      [],
      [(1, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (0, true), (1, false)],
      [(1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, true), (1, true)],
      [(1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
      [(0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true),
      (1, true), (0, true)],
      [(1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, false), (0, false), (0, false), (1, false), (0, true), (1, false)],
      [(1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (0, true), (1, true)],
      [(0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (0, false), (0,
      false), (1, false), (0, false)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1,
      true), (0, true), (1, true), (0, true), (0, true), (1, false)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false),
      (0, false), (1, false), (0, false), (1, false), (0, true), (1, true)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (0,
      true), (1, true)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (0,
      true), (1, true), (0, false), (1, true), (1, true), (0, true)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, false),
      (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1,
      false), (0, true), (1, false)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, false), (0, false), (0, false), (1, false),
      (0, true), (1, false)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1,
      true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (0,
      true), (1, true)],
      [(0, true), (1, true), (4, false), (4, false), (0, false), (4, false), (1, false), (0,
      false), (1, true), (1, true), (0, true), (0, false), (1, false), (1, false), (0, true),
      (1, false), (0, false), (0, false), (0, false), (1, false), (0, false)]]]

@[expose] def burnsideF48t_u52eXW : List (List (Fin 5 × Bool)) :=
  [
    [(4, true), (2, true), (0, false), (0, false), (0, false), (2, false), (2, false)],
    [(2, false), (4, false), (0, false), (0, false), (0, false)],
    [(2, false), (4, false), (2, true)],
    [(2, true), (0, true), (1, true), (1, true), (0, false), (2, false), (1, false), (2, true),
    (0, true), (4, true), (2, false), (2, false)]]

@[expose] def burnsideF48t_u52eYW : List (List (Fin 5 × Bool)) :=
  [
    [(3, false), (4, false), (3, false), (0, false), (0, false), (0, false), (3, true)],
    [(3, true)]]

@[expose] def burnsideF48t_u52eR1 : List (List (Fin 5 × Bool)) :=
  [
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
    [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true)],
    [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    [(2, true), (2, true), (0, false), (0, false), (0, false), (2, false), (2, false), (0,
    false), (0, false), (0, false)],
    [(2, false), (1, false), (1, false), (2, true), (1, false), (2, true), (1, false), (1,
    false), (2, false), (1, false)],
    [(1, true), (0, false), (2, true), (1, true), (2, true), (0, false), (1, true), (1, true),
    (0, true), (1, true)],
    [(2, false), (2, false), (0, false), (1, false), (2, true), (0, false), (2, false), (1,
    true), (0, false), (2, true), (1, true)],
    [(0, false), (2, true), (2, true), (0, false), (2, true), (2, true), (0, false), (1, false),
    (1, false), (2, true), (1, false), (2, true)],
    [(2, true), (2, true), (0, true), (2, false), (2, false), (0, false), (1, true), (0, true),
    (2, false), (1, false), (2, false), (1, true)],
    [(2, false), (2, false), (0, true), (2, true), (2, true), (0, false), (1, false), (2, true),
    (1, false), (2, true), (0, false), (1, true)],
    [(2, false), (2, false), (0, false), (2, true), (2, true), (0, true), (2, false), (2,
    false), (0, true), (0, true), (2, true), (2, true), (0, true)],
    [(0, true), (2, true), (2, true), (0, true), (1, false), (0, false), (1, false), (2, false),
    (0, true), (2, false), (1, true), (0, true), (2, true)],
    [(0, true), (2, true), (2, true), (0, false), (2, true), (2, true), (0, true), (1, true),
    (0, false), (2, false), (2, false), (0, false), (1, true)],
    [(2, false), (2, false), (0, false), (0, false), (1, true), (0, true), (2, false), (1,
    false), (2, false), (0, false), (1, false), (1, false), (0, true), (1, true)],
    [(2, true), (2, true), (0, true), (2, true), (2, true), (0, false), (2, true), (2, true),
    (1, true), (0, true), (1, false), (1, false), (0, false), (1, true)],
    [(2, false), (2, false), (0, true), (0, true), (2, true), (2, true), (0, false), (2, true),
    (2, true), (1, true), (0, false), (1, false), (0, false), (1, false)],
    [(2, false), (2, false), (0, true), (0, true), (2, false), (2, false), (0, false), (2,
    false), (2, false), (0, false), (2, false), (2, false), (0, false), (2, false), (2, false),
    (0, false), (2, false), (2, false), (0, false)],
    [(4, true), (4, true)],
    [(4, true), (0, true), (4, false), (1, true), (1, true), (0, false), (2, false), (2, false),
    (0, false), (2, false), (2, false), (0, false)],
    [(4, true), (1, true), (4, false), (2, true), (2, true), (0, false), (2, false), (2, false),
    (1, false), (0, true), (1, false)],
    [(4, true), (2, true), (4, false), (0, true), (0, true), (0, true), (2, true), (0, true),
    (0, true), (0, true)]]

@[expose] def burnsideF48t_u52eR2 : List (List (Fin 5 × Bool)) :=
  [
    [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    [(3, true), (3, true), (3, true), (3, true), (3, true), (3, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, false), (3, true), (1, true), (1, true), (3, false), (0, true)],
    [(3, false), (3, false), (1, false), (1, false), (0, false), (0, false), (3, true), (0,
    true), (3, false)],
    [(0, false), (3, false), (0, true), (3, true), (0, true), (3, false), (0, true), (3, true),
    (0, false)],
    [(1, false), (1, false), (1, false), (3, false), (3, false), (1, false), (1, false), (1,
    false), (3, true), (3, true)],
    [(1, true), (3, true), (3, true), (1, false), (1, false), (3, false), (3, false), (1,
    false), (3, false), (3, false)],
    [(3, true), (1, false), (1, false), (3, true), (0, true), (1, true), (0, true), (1, false),
    (1, false), (0, false), (1, false), (0, true), (0, true)],
    [(1, true), (3, false), (0, true), (3, false), (0, false), (3, false), (1, true), (1, true),
    (3, false), (1, false), (1, false), (0, false), (1, true)],
    [(1, false), (1, false), (0, false), (1, false), (1, false), (3, true), (0, true), (3,
    false), (3, false), (0, false), (3, false), (1, true), (1, true), (0, true)],
    [(0, false), (3, true), (3, true), (1, false), (0, true), (3, false), (3, false), (1, true),
    (3, false), (1, true), (3, false), (0, true), (1, true), (3, true)],
    [(3, false), (0, true), (3, true), (0, false), (3, true), (3, true), (1, false), (3, true),
    (3, true), (1, true), (0, false), (3, false), (1, true), (1, true), (3, false)],
    [(3, false), (3, false), (1, true), (3, true), (1, false), (3, false), (0, true), (3, true),
    (0, false), (1, true), (1, true), (3, true), (3, true), (0, false), (1, true), (3, true),
    (1, false)],
    [(1, true), (3, false), (3, false), (0, false), (3, true), (3, true), (1, false), (0, true),
    (3, false), (1, false), (1, false), (3, true), (0, true), (1, true), (0, false), (3, false),
    (1, true), (1, true), (3, false)],
    [(4, true), (4, true)],
    [(4, true), (0, true), (4, false), (1, false), (3, true), (3, true), (1, true), (0, true),
    (1, true), (1, true)],
    [(4, true), (1, true), (4, false), (0, true), (0, true), (1, true), (0, false), (0, false),
    (3, false), (1, true), (1, true), (3, false), (1, false)],
    [(4, true), (3, true), (4, false), (1, true), (1, true), (3, true), (3, true), (0, true),
    (3, true), (0, true)]]

@[expose] def burnsideF48t_u52eCands : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 0, 1), (0, 0, 1, 1), (0, 0, 2, 1), (0, 1, 0, 1), (0, 1, 3, 1), (0, 1, 6, 1), (1, 0, 0,
  1), (1, 0, 1, 1), (1, 0, 2, 1), (1, 0, 15, 1), (1, 0, 16, 1), (1, 0, 17, 1), (1, 1, 0, 1), (1,
  1, 3, 1), (1, 1, 6, 1), (2, 0, 0, 1), (2, 0, 1, 165), (2, 0, 2, 1), (2, 1, 0, 1), (2, 1, 3,
  1), (2, 1, 6, 165), (3, 0, 0, 165), (3, 0, 1, 1), (3, 0, 2, 1), (3, 0, 15, 1), (3, 0, 16, 1),
  (3, 0, 17, 1), (3, 1, 0, 1), (3, 1, 3, 165), (3, 1, 6, 1)]

end CFSG.ASVolI
