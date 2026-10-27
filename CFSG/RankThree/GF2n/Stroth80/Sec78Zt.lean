module

public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec78VtIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOmega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7Zt_of_inputs (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA7 : Sec7AExistsStatement)
    (hA8 : Sec8AExistsStatement) (h56 : Stroth56NatStatement)
    (hPtsΩ : Sec5NatPointsOmegaStatement) (hPtsSp : Sec5NatPointsSpStatement) :
    Sec7ZtStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  obtain ⟨hRle, hV⟩ := sec7ctr_zt_omega h34 h51 h52a hA7 sec7VtIrred_holds G M Q Z B hc n t hs Z0
    hZ0 s hsZ hsQ
  obtain ⟨r, hr⟩ := hA7 G M Q Z B hc n t hs
  have hsL : s ∈ LB M Q B :=
    sec7ctr_Z0_le_LB h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 (sec7ctr_Z0_le_CN hc hs hZ0) hsZ
  by_cases hom : OmegaMinusNat hc t 2
  · exact ⟨le_antisymm (sec7ctr_Rt_le_om4 h34 h310 hA7 hA8 hPtsΩ hPtsSp hc hs hom hr hsL hsQ
      hRle hV) hRle, hV⟩
  · have h56' : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
        ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z :=
      fun m hm hsub => h56 G M Q Z B hc n t hs hom m hm hsub
    exact ⟨le_antisymm (sec7ctr_Rt_le_of_56 hc h56' hs.toSec5.mem hV) hRle, hV⟩

end CFSG.RankThree.GF2n.Stroth80
