module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4

variable {G : Type}

theorem comm_le_of_bil [Group G] {P L E V Z : Subgroup G} [Finite ↥P]
    (hE : A5Pre P L E V) (hV : A5Pre P L V Z) (_hE2 : IsPGroup 2 E)
    (hEV : NatQuot L E V 2) (hVZ : NatQuot L V Z 2) (hcomm : ⁅E,E⁆ ≤ V)
    (hcent : ⁅E,V⁆ ≤ Z) : ⁅E,E⁆ ≤ Z :=
  comm_le_of_natPre le_rfl
    ⟨hE.le, hE.norm_L, hE.norm_E, hE.norm_K, hE.sec, hE.card, hE.core, hE.quot, hE.nontriv⟩
    ⟨hV.le, hV.norm_L, hV.norm_E, hV.norm_K, hV.sec, hV.card, hV.core, hV.quot, hV.nontriv⟩
    hEV hVZ hcomm hcent

end CFSG.Quasithin.St84
