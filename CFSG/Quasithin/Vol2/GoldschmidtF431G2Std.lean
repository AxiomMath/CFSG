module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2StdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2StdLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2NFLieStd

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.Sec53F.G2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


theorem g2_std {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    ∃ (z t v nr na : C K) (V L Zd Qd Xd Yd : Subgroup (C K)),
      StdTwo (C K) (U K) (Pmin K ⟨1, by decide⟩) (Pmin K ⟨0, by decide⟩) z t ∧
      StdLoc (C K) (U K) z t V L ∧
      StdOrient (C K) (U K) (Pmin K ⟨1, by decide⟩) (Pmin K ⟨0, by decide⟩) z t v nr na
        Zd Qd Xd Yd (Nat.card K) 2 :=
  ⟨xc 1, xv 1, xu 1, NFLie.nrC K, NFLie.naC K, V K, Cent.La K, Xc K, Q1 K, Xa K, Xb K,
    g2_stdTwo hf hK, g2_stdLoc hf hK, NFLie.stdOrient_g2 hf hK⟩

end CFSG.Quasithin.H13.F431.G2
