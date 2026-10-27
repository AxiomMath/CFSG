module

public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs
public meta import CFSG.Monster.B.TwoA.Sp8.P0StructInputs

public section

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

@[expose] def nfWord (g : ℕ × ℕ × ℕ) : List XLetter := lWord g.1 ++ tWord g.2.1 ++ uProd g.2.2

@[expose] def gensA1 : List (ℕ × ℕ × ℕ) :=
  [(14479, 0, 0), (52645, 0, 0), (64475, 0, 0), (52504, 0, 0), (43198, 0, 0),
   (0, 1, 0), (0, 2, 0), (0, 4, 0), (0, 8, 0), (0, 16, 0), (0, 32, 0), (0, 64, 0), (0, 128, 0),
   (0, 256, 0)]

@[expose] def gensA2 : List (ℕ × ℕ × ℕ) :=
  [(57366, 407, 268), (4161, 192, 195), (200, 18, 8), (4251, 242, 207), (77, 87, 11),
   (132, 43, 0), (12, 39, 0), (68, 267, 0), (4, 52, 0),
   (0, 2, 0), (0, 48, 0), (0, 304, 0), (0, 268, 0), (0, 271, 0)]

@[expose] def gensA4' : List (ℕ × ℕ × ℕ) :=
  [(49360, 164, 333), (49180, 155, 325), (57370, 440, 203), (8340, 275, 389), (148, 15, 5),
   (132, 280, 0), (136, 274, 0), (68, 257, 0), (4, 62, 0),
   (0, 284, 0), (0, 48, 0), (0, 63, 0), (0, 288, 0), (0, 2, 0)]

@[expose] def xWord : List XLetter := [.lift 27, .lift 28, .lift 27]

@[expose] def yWord : List XLetter := [.lift 30]

@[expose] def xT9 : List ℕ := [1, 2, 4, 32, 16, 60, 65, 131, 256]

@[expose] def yT9 : List ℕ := [1, 2, 4, 12, 20, 56, 64, 128, 260]

end CFSG.Monster.B.TwoA.Sp8.WordRel
