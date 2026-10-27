module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier7
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddFinal
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26A_Holds
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Hss33Final
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

theorem F53.Stellmacher.hss42CardGt_holds : F53.Stellmacher.Hss42CardGt :=
  fun _ _ _ _ _ _ hA => F53.Stellmacher.hss42CardGtAt_of_hss28 hA
    (F53.Stellmacher.hss28At_of_hss26A hA (F53.Stellmacher.hss26A_holds _ _ _ _ hA))

theorem F53.Stellmacher.f53Dichotomy2_of_frontier13 (h35o : F53.Stellmacher.Hss35Orth)
    (h36n : F53.Stellmacher.Hss36Nat) : F53Dichotomy2 :=
  F53.Stellmacher.f53Dichotomy2_of_frontier4
    (fun G _ _ H M S hA hb δ μ U hSig hQ _ _ =>
      F53.Stellmacher.hss26A_holds G H M S hA hb δ μ U hSig hQ)
    (F53.Stellmacher.Hss33_of_hss26A F53.Stellmacher.hss26A_holds)
    (F53.Stellmacher.Hss34_of_hss26A F53.Stellmacher.hss26A_holds) h35o h36n
    F53.Stellmacher.hss42CardGt_holds
    (F53.Stellmacher.S43.Odd.hss43_of F53.Stellmacher.hss26A_holds)

end CFSG.Quasithin
