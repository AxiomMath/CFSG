module

public import CFSG.RankThree.PartTwo.Sec20.Step2051Proof
public import CFSG.RankThree.PartTwo.Sec20.Item20Res8ProofIndexC
public import CFSG.RankThree.PartTwo.Sec20.Step2051SylowProof
public import CFSG.RankThree.PartTwo.Sec20.Step2053Proof
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofThree
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenG
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSevenY
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofFrontier
public import CFSG.RankThree.PartTwo.Sec20.SimsStep2053
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Orbit
import CFSG.RankThree.PartTwo.Sec3.Sims321Count

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Step2051

theorem step2051_of_sec18 (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h187 : Sec18.Item187) (h189 : Sec18.Item189) (hO2 : Step189O2) : Step2051 :=
  step2051_of h189
    (step2051Index_of kFactL3ParabolicOrbit_holds
      (step2051IndexN_of (step2051IndexC_of h187 hO2) h187))
    (step2051Sylow_of h1812 h184)

end Step2051

theorem step2053_of_item316 (h189 : Sec18.Item189)
    (h316 : Sec19.Item316) : Step2053 :=
  step2053_of h189 (step2053L2_of_localCGT h316)

section Item206

theorem item206One_of_sec18 (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h185 : Sec18.Item185) (h189 : Sec18.Item189) (h204 : Item204One) (h2051 : Step2051)
    (h2053 : Step2053) : Item206One :=
  item206One_of_thompson h1812 h184 (item203One1_of_items h1812 h184 h185 h189) h204 h2051 h2053
    h189 Sec3.Sims321.item321Count_holds

end Item206

section Item207

theorem item207One_of_sec18 (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h184_5 : Sec18.Item184_5) (h184_6 : Sec18.Item184_6) (h185 : Sec18.Item185)
    (h186 : Sec18.Item186H) (h189 : Sec18.Item189) (h1810 : Sec18.Item1810Hyp)
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo)
    (hK : KF207Theta) (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053) :
    Item207One :=
  item207One_of_items_gen h204 h2051 h2053 h189 Sec3.Sims321.item321Split_holds h1812 h184
    (item206One_of_sec18 h1812 h184 h185 h189 h204 h2051 h2053)
    (step207K0_of_cyclic h186 h1812 h184 (item203One1_of_items h1812 h184 h185 h189) h204 h2051
      h2053 h189 Sec3.Sims321.item321Split_holds
      (step207YCyclic_of h432 h41 hG2 h184_5 h184_6 h1810 h204 h2051 h2053) hK)

end Item207

theorem item209One_of_sec18 (h184 : Sec18.Item184_1) (h207 : Item207One) (h208 : Item208One) :
    Item209One :=
  item209One_of_step209LCentral h207 h208 (step209LCentral_of_item184 h184)

end CFSG.RankThree.PartTwo.Sec20
