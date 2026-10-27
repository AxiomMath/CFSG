module

public import CFSG.Monster.Existence.TwoPoint.HNRigid

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.AxisCount

@[expose, noinline] def visConjCheck (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all Native.Gen.isVis && checkP2 (HS.pw w₁) (HS.pw w₂)

@[expose] def permMonoA : Array ℕ :=
  #[0, 1, 17, 11, 6, 15, 21, 3, 18, 5, 8, 7, 16, 13, 14, 9, 20, 23, 10, 19, 12, 4, 22, 2]

@[expose] def wordMonoA : List Native.Gen := [.perm permMonoA]

@[expose] def wordKA : List Native.Gen :=
  [.sign 3901, .rho (false, 1488, 3839), .rho (false, 0, 8), .rho (false, 0, 34),
    .perm #[7, 20, 9, 8, 23, 4, 12, 14, 3, 16, 10, 15, 19, 0, 11, 13, 2, 1, 21, 5, 17, 18, 22, 6],
    .xi, .rho (false, 0, 36),
    .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
    .xi, .rho (false, 0, 18),
    .perm #[0, 2, 5, 10, 6, 11, 17, 16, 7, 8, 13, 15, 21, 22, 9, 4, 12, 20, 1, 18, 19, 3, 14, 23]]

@[expose] def permMonoC : Array ℕ :=
  #[20, 15, 14, 19, 21, 8, 18, 9, 12, 10, 7, 0, 5, 4, 17, 23, 3, 2, 22, 16, 11, 13, 6, 1]

@[expose] def wordMonoC : List Native.Gen := [.perm permMonoC]

@[expose] def wordKC : List Native.Gen :=
  [.sign 2580, .rho (false, 2287, 557), .rho (false, 0, 2313), .rho (false, 0, 38),
    .perm #[2, 16, 14, 3, 20, 15, 19, 22, 10, 13, 17, 8, 6, 12, 18, 5, 0, 11, 4, 21, 1, 7, 9, 23],
    .xi, .rho (false, 0, 24),
    .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
    .xi, .xi, .rho (false, 0, 34),
    .perm #[0, 2, 9, 11, 16, 22, 19, 23, 5, 14, 7, 12, 1, 8, 10, 3, 4, 6, 13, 15, 18, 20, 21, 17]]

end CFSG.Monster.Existence
