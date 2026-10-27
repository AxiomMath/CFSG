module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Cells
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsCert
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA7Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA6FullK
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellD7FullE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_smallCellsEK_of
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) :
    GGQ2S08SmallCellsEK := by
  intro t r s h
  simp only [ggQ2S08CellList, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA4 hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA5a hLB hP hRig hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA5b hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA5c hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA5d hLB hP hΓi hTBN)
  · exact GGQ2S08CellEK.of_halves (ggQ2s08_cellE_twA6 hLB hP hRig hΓi hTBN)
      (ggQ2s08_cellK_twA6 hLB hP hRig hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA7 hLB hP hRig hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA8a hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA8b hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA8c hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twA8d hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inl rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inl rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inl rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inl rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inl rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inr rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inr rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inr rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inr rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK
      (ggQ2s08_cell_BC hLB hP hΓi hTBN (Or.inr rfl) (by norm_num) (by norm_num))
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_D hLB hP hΓi hTBN (Or.inl rfl) (by norm_num))
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_D hLB hP hΓi hTBN (Or.inl rfl) (by norm_num))
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_D hLB hP hΓi hTBN (Or.inl rfl) (by norm_num))
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_D hLB hP hΓi hTBN (Or.inr rfl) (by norm_num))
  · exact ggQ2s08_cell_twD7 hLB hP hΓi hTBN
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_F4 hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twE6a hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twE6b hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twE6c hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_twE6d hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_E7 hLB hP hΓi hTBN)
  · exact GGQ2S08Cell.toEK (ggQ2s08_cell_E8 hLB hP hΓi hTBN)

theorem ggQ2s08_reflEKSmall_holds
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr)
    (hTB : GGQ2TableBI1Fail) : GGQ2ReflEKSmallInput :=
  ggQ2s08_reflEKSmall_of_cellsEK hTB (ggQ2s08_smallCellsEK_of hLB hP hRig hΓi hTBN)

end CFSG.StandardType

end
