module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofL34
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.Sec15.Item1510Proof
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

theorem step163NoL34_of
    (h131 : Item131) (h1513 : Item1513R) (h1510 : Item1510R)
    (hBr : Step169TwoBridge) : Step163NoL34 := by
  intro G _ _ A c L h hφ h9 hY0
  obtain ⟨φ⟩ := hφ
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨hprod, hirr⟩ : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, hprod, hcase⟩ |
        ⟨-, -, he, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
    · exact ⟨hprod, Proof1514.isIrreducibleOn_of_cases131 hD hcL h9 hcase⟩
    · exact (Proof1510.false_of_prod_cases_of_l34 hD φ (Or.inr he)).elim
    · exact (Proof1511.false_of_card_nine_of_isZ3PGLThreePi hD hcL h9 hPGL).elim
    · exact (hcL hcL').elim
  rcases h1513 G A c L h hY0 hirr h9 with ⟨⟨e⟩, -⟩ | hΩ
  · have h1 := Nat.card_congr (φ.symm.trans e).toEquiv
    rw [KFacts.KS14.card_projSL_three_four,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h1
    norm_num at h1
  ·
    exact false_of_l34 h φ hΩ hprod (h1510 G A c L h) hBr

end CFSG.RankThree.PartTwo.Sec16
