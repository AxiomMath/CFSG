module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_or_of_isNaturalClassicalModule_of_rankThree {H S P : Subgroup (MulAut W)}
    {k n : ℕ} (hnat : IsNaturalClassicalModule H k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n)
    (hrank3 : (IsSLn ↥H 4 k ∧ BinaryNaturalSL H ⊤ ⊥ 4 k) ∨
      (IsOmegaPlus ↥H 6 k ∧ NatOmegaPlus H ⊤ ⊥ 6 k) ∨ (IsSpn ↥H 6 k ∧ NatSpn H ⊤ ⊥ 6 k) ∨
      (IsOmega8m ↥H k ∧ NatOmegaMinus H ⊤ ⊥ 8 k) → n = k) :
    n = k ∨ (IsOmegaMinus ↥H 4 k ∧ n = 2 * k) := by
  rcases hnat with h | h | h | h | h | h | h | h
  · exact Or.inl (nParam_eq_of_natL2 h hperf hS hBP hPH hcomm hN)
  · exact Or.inr ⟨h.1, nParam_eq_two_mul_of_natOmegaMinusFour h hperf hS hBP hPH hcomm hN⟩
  · exact Or.inl (nParam_eq_of_natOmegaPlusFour h hk hperf hS hBP hPH hcomm hN)
  · exact Or.inl (nParam_eq_of_natSp4 h hk hperf hS hBP hPH hcomm hN)
  · exact Or.inl (nParam_eq_of_natSL3 h hk hperf hS hBP hPH hcomm hN)
  · exact Or.inl (nParam_eq_of_natSU4 h hk hperf hS hBP hPH hcomm hN)
  · exact Or.inl (nParam_eq_of_natOmegaMinusSix h hk hperf hS hBP hPH hcomm hN)
  · exact Or.inl (hrank3 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
