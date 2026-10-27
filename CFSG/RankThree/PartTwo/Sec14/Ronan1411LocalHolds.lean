module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1411Holds
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofWGamma
import CFSG.RankThree.PartTwo.Sec14.Wales1411WJ2
import CFSG.RankThree.PartTwo.Sec14.Ronan143QSylow1411X
import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1411

public section

namespace CFSG.RankThree.PartTwo.Sec14

theorem claim1411NonsolvWR_holds
    : Claim1411NonsolvWR := by
  obtain ⟨h45, h48, -, h422, -, -, -, h131, h134, -, h142⟩ := Ronan148M.closedInputs
  have h143 := Ronan148M.item143QS14_holds
  have hbot := Ronan149.item145BotS14_holds
  have hKL := Sec4.Ronan148L.kl3HessTori_holds
  exact claim1411NonsolvWR_of_jl3 h131 h142 Sec15.Proof148FourK.item146S14_holds hbot
    (claim1411NonsolvWPointJL3R_of_odd h131 h142 hbot
      (claim1411NonsolvWPointJL3OddR_of_l3odd h142 hbot Wales1411W.etrans2_J2
        (claim1411NonsolvWPointL3OddR_of_field h131 h142 hbot (kl3HessETrans2_of_tori hKL)
          (claim1411NonsolvWPointL3FieldR_of_tori h131 h142 hbot h422 h45 hKL
            (claim1411NonsolvWPointHJConfR_of_core h142 hbot Wales1411W.etrans2_J2 h143 h134 h48
              (claim1411HJConfCoreR_of_kfact Ronan148M.item148R_holds h143 h134 h48 hbot
                (ks1411HJCore_of_L37 Ronan1411L37.ks1411HJCoreL37)))))))

theorem claim1411NonsolvXR_holds
    : Claim1411NonsolvXR := by
  obtain ⟨h45, -, -, h422, -, -, -, h131, -, -, h142⟩ := Ronan148M.closedInputs
  exact Ronan143Q.claim1411NonsolvXR_of_sylow_item143Q h131 h142 Ronan148M.item143QS14_holds
    Sec15.Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds h422 h45

theorem claim1411LocalR_holds
    : Claim1411LocalR :=
  claim1411LocalR_of Sec15.Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds
    claim1411NonsolvWR_holds claim1411NonsolvXR_holds

theorem item1411_1S17_holds
    : Item1411_1S17 :=
  item1411_1S17_of item1411_1R_holds

theorem step1411WGammaR_holds
    : Step1411WGammaR :=
  step1411WGammaR_of claim1411LocalR_holds

theorem step1411WGammaLaR_holds
    : Step1411WGammaLaR :=
  step1411WGammaLaR_of step1411WGammaR_holds

end CFSG.RankThree.PartTwo.Sec14
