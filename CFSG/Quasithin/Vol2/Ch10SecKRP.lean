module

public import CFSG.Quasithin.Vol2.Ch10SecKRPc
public import CFSG.Quasithin.Vol2.Ch10SecB6Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem fact10_2_6Pair_of_pairCent (hPC : A312PairCent) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) : Fact10_2_6Pair := by
  intro Q _ hQ S K B₁ B₂ hS hK hB₁ hB₂ hN₁ hN₂ hB₁K hB₂K hc ⟨e⟩
  by_cases hq : CFSG.IsQuasisimple ↥K
  · exact KRP.false_of_quasisimple hPC hQ hS hK hB₁ hB₂ hN₁ hN₂ hB₁K hB₂K hc e hq
  · exact KRP.false_of_nonquasi hSL2 h36 hQ hS hK hB₁ hB₂ hB₁K hB₂K (hc.trans inf_le_left) hq

end CFSG.Quasithin.Vol2.Ch10.SecB
