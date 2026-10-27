module

public import Certificates.Data.ONanG28T

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28.SU

@[expose] def suW : List (List ℕ) := [
  gW[0]!, gW[1]! ++ gW[0]! ++ (gW[1]!).reverse, gW[1]! ++ gW[1]!, gW[2]!,
  gW[1]! ++ gW[2]! ++ (gW[1]!).reverse, gW[3]! ++ (gW[1]!).reverse, gW[1]! ++ gW[3]!]

@[expose] def suP : Array ℕ := #[
  0, 6, 3, 1, 7, 3, 4, 2, 4, 0, 1, 3, 1, 7, 3, 4, 4, 2, 6, 6, 1, 2, 3, 4, 6, 1, 7, 3, 6, 4, 6, 4,
  4, 4, 2, 1]

@[expose] def suPi : Array ℕ := #[
  6, 1, 4, 6, 2, 7, 6, 6, 6, 0, 4, 1, 2, 3, 4, 1, 0, 4, 1, 7, 4, 3, 4, 3, 4, 4, 1, 3, 3, 2, 3, 6,
  2, 7, 1, 4]

end CFSG.AGLEmbedding.KFactProofs.G28.SU
