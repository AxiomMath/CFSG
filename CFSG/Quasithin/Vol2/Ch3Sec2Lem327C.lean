module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327
public import CFSG.Quasithin.Vol2.Ch3T326S

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt3_2_7C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∨
      (LieModel ↥(autOn L (conjClosure V₀ T)) .PSL 3 2 1 ∧ L ≠ conjClosure L T ∧
        Case3_2_6_iii T L V₀) ∨
      (L ≠ conjClosure L T ∧ ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))), Case3_2_6_iv T L V₀)

theorem stmt3_2_7C_of (h325 : Stmt3_2_5) (h326 : Stmt3_2_6C) : Stmt3_2_7C := by
  intro G _ _ T L V₀ hfsu
  by_cases hL : L = conjClosure L T
  · exact Or.inl (isTISetUnder_of_stmt3_2_5 h325 hfsu hL)
  obtain ⟨-, hcomm, -, hcases⟩ := h326 G T L V₀ hfsu hL
  rcases hcases with ⟨-, -, -, -, -, -, -, hVM, -⟩ | ⟨-, -, hVM, -⟩ | ⟨-, hc⟩
  · exact Or.inl (isTISetUnder_of_eq_conjClosure hVM)
  · exact Or.inl (isTISetUnder_of_eq_conjClosure hVM)
  · rcases hc with ⟨-, -, -, hVM⟩ | ⟨-, hVM, -⟩ | hiii | hiv
    · exact Or.inl (isTISetUnder_of_eq_conjClosure hVM)
    · exact Or.inl (isTISetUnder_of_eq_conjClosure hVM)
    · exact Or.inr (Or.inl ⟨lieModel_autOn_fsuV_of_case3_2_6_iii hfsu hiii, hL, hiii⟩)
    · exact Or.inr (Or.inr ⟨hL, hcomm, hiv⟩)

end CFSG.Quasithin.H13
