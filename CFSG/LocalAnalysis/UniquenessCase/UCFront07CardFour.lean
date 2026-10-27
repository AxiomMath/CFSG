module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Core3
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Bad

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.Open (uniqueFourUnique)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Sec7Core4 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree normalizer_le_of_r6_3)

variable {G : Type} [Group G] [Finite G]

theorem r74Card_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hC : TheoremCAt S.M) : R74Card (UC6.dataOfSetup4 hS hU S) := by
  intro p H hH
  obtain ⟨hpp, hp2, hsp, htop, hHM, hrank⟩ := hH
  let k : Sec7Core4 G :=
    Sec7Core4.ofHuniq (UC6.dataOfSetup4 hS hU S).standing hU S.M S.maxLocal p hpp hp2 hsp
      fun T hT hT2 hT3 => normalizer_le_of_r6_3 _ (UC6.r6_3_dataOfSetup4 hS hU S hC) hpp hp2 hsp
        hT hT2 hT3
  have hk : k.Config H := ⟨htop, hHM, hrank⟩
  by_cases hp3 : p = 3
  · exact k.step74w_of_stronglyEmbeddedThree hp3 hK3 H hk
  have h5 : 5 ≤ k.p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3
  exact (k.step74_of_kIDExcluded h5
    (PartOne.Section7.R72.kIDExcluded_of_setup4 hU S hσ hB k rfl h5) hSE).toWeak H hk

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
