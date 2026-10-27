module

public import Certificates.Data.Kernel.M24QSpan

public section

namespace CFSG.KD.Fi24Pkg

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.S125KG.M24
open CFSG.QuasithinUnique.Ch1.SporLat.M24

@[expose] def w5 : List ℕ :=
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0]

@[expose] def w11 : List ℕ :=
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 0, 1]

@[expose] def s0T : List ℕ := sTabsK.getD 0 []

@[expose] def s1T : List ℕ := sTabsK.getD 1 []

@[expose] def xT : List ℕ := compTab (wTab w5) (wTab w5)

@[expose] def yT : List ℕ := compTab s0T (compTab (wTab w5) (compTab s0T (wTab w5)))

@[expose] def aT : List ℕ := compTab s1T (wTab w11)

@[expose] def gT : List ℕ := s1T

@[expose] def cubeT (t : List ℕ) : List ℕ := compTab t (compTab t t)

@[expose] noncomputable def fi24WordsOK (_ : Unit := ()) : Bool :=
  m24LatK.mw[5]! == [w5] && m24LatK.mw[11]! == [w11]

@[expose] def fi24NineOK (x y : List ℕ) : Bool :=
  cubeT x == List.range 24 && cubeT y == List.range 24 && compTab x y == compTab y x &&
    !(x == List.range 24) && !(y == List.range 24) && !(y == x) && !(y == compTab x x)

@[expose] def fi24ThreeOK (a g : List ℕ) : Bool :=
  cubeT a == List.range 24 && !(a == List.range 24) && compTab g a == compTab (compTab a a) g

end CFSG.KD.Fi24Pkg
