module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNOmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNLeast
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem eq_or_natOmegaMinus_of_parN {W : Type} [CommGroup W] [Finite W]
    {H R S P : Subgroup (MulAut W)} {k n : ℕ}
    (hnat : IsNaturalClassicalModule H k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hRH : R ≤ normalizer (H : Set (MulAut W)))
    (hRS : R ≤ normalizer (S : Set (MulAut W)))
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hRP : R ≤ normalizer (P : Set (MulAut W))) (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥)
    (hmin : ∀ Q : Subgroup (MulAut W), Q < P → H ⊓ normalizer (S : Set (MulAut W)) ≤ Q →
      R ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥)
    (hN : NParam (Hinf P) n) :
    n = k ∨ (IsOmegaMinus ↥H 4 k ∧ NatOmegaMinus H ⊤ ⊥ 4 k ∧ n = 2 * k) := by
  obtain ⟨hL2, hO4m, -, hSp4, hSL3, hSU4, hO6m, hSL4, hO6p, hSp6, hO8m⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  rcases hnat with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (eq_of_forall_minimal_eq_top hS hRH hRS hBP hPH hcomm hmin hN (hL2 h))
  · exact Or.inr ⟨h.1, h.2,
      eq_of_forall_minimal_eq_top hS hRH hRS hBP hPH hcomm hmin hN (hO4m h)⟩
  · exact Or.inl (eq_of_omegaPlusFour h.1 h.2 hk hperf hS hRH hRS hBP hPH hRP hcomm hmin hN)
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natSp4 h.2 hS.toSylow) (hSp4 h))
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_binaryNaturalSL (by norm_num) h.2 hS.toSylow) (hSL3 h))
  · have hline := hSU4 h
    obtain ⟨a, -, -, hNat⟩ := h
    exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natSU4 hNat hS.toSylow) hline)
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natOmegaMinusSix h.2 hS.toSylow) (hO6m h))
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_binaryNaturalSL (by norm_num) h.2 hS.toSylow) (hSL4 h))
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natOmegaPlusSix h.2 hS.toSylow) (hO6p h))
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natSp6 h.2 hS.toSylow) (hSp6 h))
  · exact Or.inl (eq_of_least_of_line hS hRH hRS hBP hPH hcomm hmin hN hk
      (leastParabolic_natOmegaMinusEight h.2 hS.toSylow) (hO8m h))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
