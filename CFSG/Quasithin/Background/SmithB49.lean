module

public import CFSG.Quasithin.Background.SmithB49Off
public import CFSG.Quasithin.Background.SmithB49N4
public import CFSG.Quasithin.Background.SmithB49N5
public import CFSG.Quasithin.Background.SmithB49D5
public import CFSG.Quasithin.Background.SmithB51LnInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln CFSG.Quasithin.B5.B49

theorem asB492Split_holds : AsB492Split := by
  intro V _ _ hV n hn L U π hU hQ hA
  rw [← realM_mat_iff] at hU
  rcases hQ with hQ | hQ
  · rw [← realM_mat_iff] at hQ
    obtain ⟨D⟩ := ExtData.exists (M := matHom n) hV hU hQ
    apply D.split
    rcases hn with rfl | rfl
    · exact h1N4 D.coc_mem
    · exact h1N5 D.coc_mem
  · rw [← realM_dmat_iff] at hQ
    obtain ⟨D⟩ := ExtData.exists (M := dmatHom n) hV hU hQ
    apply D.split
    rcases hn with rfl | rfl
    · rcases h1D4 D.coc_mem with h | ⟨x₀, hx₀⟩
      · exact h
      · obtain ⟨A, hA, hq⟩ := hA
        exact (no_offender_D4 hV hU hQ D hx₀ hA hq).elim
    · exact h1D5 D.coc_mem

end CFSG.Quasithin.B5
