module

public import CFSG.RankThree.PartOne.KFOUT3.KtyRow3Done
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow4Done
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow56
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow8

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KLAY
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.N1322

theorem kf1322Kty_of_s2
    (hs2 : ∀ {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
      (hP : F4Param p a K) (v : Fin 2 → rootsOfUnity p K), v ≠ 1 →
        ((v 1 : rootsOfUnity p K) : Kˣ) = ((v 0 : rootsOfUnity p K) : Kˣ) ^ (1 + 2 ^ a) →
        RootLayer ↥(F4.reeGamma K a) p (tp4M hP v)
          ((2 ^ (2 * a + 1)) ^ 2 * (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)))) :
    KF1322Kty :=
  kf1322Kty_of_rows kf1322KtyRow3_holds (kf1322KtyRow4_of_s2 hs2) kf1322KtyRow5_holds
    kf1322KtyRow6_holds kf1322KtyRow8_holds

end CFSG.RankThree.PartOne.KFOUT3
