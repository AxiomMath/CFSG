module

public import Certificates.Data.Kernel.SmithL6K

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def gEdgeK (C I : Nat) (G : List Nat) (s u v : Nat) : Bool :=
  tvImgP C I (G.getD s 0) u == v

@[expose] def formGK (G : List Nat) (cols : List (List Nat)) : Bool :=
  G.all fun g => let T := cols.getD g []
    (List.range 20).all fun a => (List.range 20).all fun b =>
      fB (T.getD a 0) (T.getD b 0) == fB (2 ^ a) (2 ^ b)

end CFSG.SmithL6.K
