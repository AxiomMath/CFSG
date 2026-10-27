module

public import CFSG.Quasithin.Recognition.SzVBGeo

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem vBeta_nonabelian_of_bender (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hBO : ¬ IsL2Quot 2 (OTwoQuot K1) → BenderLocalFacts (K1 ⊔ S) S (conjClosure Zs L2))
    (hL24 : IsL2Quot 2 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ →
      ¬ Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)))
    (hEven : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ →
      ¬ Even (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2))) :
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ := by
  intro hab
  rcases Nat.even_or_odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) with
    hev | hodd
  · exact hEven hab hev
  · by_cases hL : IsL2Quot 2 (OTwoQuot K1)
    · exact hL24 hL hab hodd
    · exact odd_critDist_false hRO h hab (hBO hL) hodd

end CFSG.Quasithin.SzVB
