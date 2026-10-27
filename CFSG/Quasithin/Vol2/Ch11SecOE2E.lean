module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11

open Subgroup CFSG.Open CFSG.Quasithin

theorem tmpL6_4_2_13_of (h : H13.Stmt4_2_13FF) : TmpL6_4_2_13 := by
  intro G _ _ T M L I hH hI
  obtain ⟨hs, hnab, hQ, hT, hM, hTM, hLmax, hLf, hLM, hLq⟩ := hH
  obtain ⟨hIM, hLI, hconj, hO2I⟩ := hI
  have hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i := by
    intro t ht
    have h1 : L.map (MulAut.conj t⁻¹).toMonoidHom ∈ conjSubgroupsBy T L :=
      ⟨t⁻¹, T.inv_mem ht, rfl⟩
    rw [hconj] at h1
    obtain ⟨i, hi, hiL⟩ := h1
    refine ⟨i⁻¹, I.inv_mem hi, ?_⟩
    rw [CFSG.conjugate, CFSG.conjugate, inv_inv]
    exact hiL
  have hIT : ∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t := by
    intro i hi
    have h1 : L.map (MulAut.conj i⁻¹).toMonoidHom ∈ conjSubgroupsBy I L :=
      ⟨i⁻¹, I.inv_mem hi, rfl⟩
    rw [← hconj] at h1
    obtain ⟨t, ht, htL⟩ := h1
    refine ⟨t⁻¹, T.inv_mem ht, ?_⟩
    rw [CFSG.conjugate, CFSG.conjugate, inv_inv]
    exact htL
  exact h G T M L I hs hnab hQ hT hM hTM hLmax hLf hLM hLq hIM hLI hTI hIT hO2I

end CFSG.Quasithin.Vol2.Ch11
