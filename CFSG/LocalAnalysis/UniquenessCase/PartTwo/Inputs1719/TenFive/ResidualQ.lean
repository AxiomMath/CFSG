module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Ree
import CFSG.HardMathSupport.Dickson.I271.Support.CyclicCenter
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)


theorem w4Lem10_5ResidualQ_of_involQ (hGA : GriessAllModelsStatement) (h : W4Lem10_5InvolQ) :
    W4Lem10_5ResidualQ := by
  intro W _ _ hW Y L t n p e hLY hLn hF hLq hO2 hp hp2 _ hnot hm hq3
  left
  by_cases ht : t = .twistedG2
  · subst ht
    obtain ⟨-, hf1, rfl, rfl, ⟨k, rfl⟩, -⟩ := hm.admissible
    have hZ : center ↥L = ⊥ := Subgroup.card_eq_one.mp
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_card_center_eq_one hLq ⟨_, hf1, hm⟩)
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num at hq3
      · exact hk
    exact eight_le_mParam_of_ree hW hk hLY hLn hF (LieModel.of_quotient_center hZ hm)
  · have hZp : Nat.Coprime (Nat.card (center ↥L)) p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hpZ
      obtain ⟨rfl, hcases⟩ := CFSG.HardMathSupport.Dickson.I271.table_step hGA
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hLq) hp hp2
        (CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hm) hpZ
      rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact hnot ⟨rfl, rfl⟩
      all_goals norm_num at hq3
    exact eight_le_mParam_of_involInvertsGood hW hLY hLn hF hLq hO2 hp hp2 hZp
      (h _ t n p e hp2 hq3 hnot ht hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
