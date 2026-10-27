module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecBasic
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplit
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecFix
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecNatE

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem G2qLocalData.commutator_pCoreOf_right (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2 := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  rcases c.commutator_inf_W_eq_or (by omega) hH hD h1 h2 with hsplit | hW
  · exact (c.false_of_split_of_fix hf hH hD h1 h2 hsplit
      (hD.commutator_mem_centerOf_left_of_mem_inf hH h1 h2
        (c.commute_of_commutator_inf_W_eq hD hsplit))
      (c.commutator_commutator_mem_centerOf_left hH hD h1 h2 hsplit)
      (hD.mem_centerOf_left_of_fixed (by omega) hH h1 h2)).elim
  · exact c.commutator_eq_of_W_le hW

end CFSG.Quasithin.F112R.St84

end
