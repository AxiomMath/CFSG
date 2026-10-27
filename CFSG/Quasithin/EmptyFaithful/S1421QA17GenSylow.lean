module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17GenMap
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S1421QA17

theorem isSylowTwoOf_top_map_of_mulEquiv {Y A : Type*} [Group Y] [Group A] (φ : Y ≃* A)
    {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
  obtain ⟨-, hT2, hidx⟩ := hT
  refine ⟨le_top, hT2.map φ.toMonoidHom, ?_⟩
  have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  have e2 : ((T.map φ.toMonoidHom).subgroupOf ⊤).index = (T.map φ.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have e3 : (T.map φ.toMonoidHom).index = T.index := Subgroup.index_map_equiv T φ
  rw [e2, e3]
  rwa [e1] at hidx

open scoped commutatorElement in
theorem commutatorElement_mem_of_index_two {G : Type*} [Group G] {J : Subgroup G}
    (hJ : J.index = 2) (g₁ g₂ : G) : ⁅g₁, g₂⁆ ∈ J := by
  simp only [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hJ, inv_mem_iff]
  tauto

theorem le_of_commutator_eq_self_of_index_two {G : Type*} [Group G] {J N : Subgroup G}
    (hJ : J.index = 2) (hN : ⁅N, N⁆ = N) : N ≤ J :=
  hN.symm.le.trans (Subgroup.commutator_le.mpr fun g₁ _ g₂ _ =>
    commutatorElement_mem_of_index_two hJ g₁ g₂)

theorem map_map_symm_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (K : Subgroup G) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K :=
  (Subgroup.map_symm_eq_iff_map_eq K).mpr rfl

theorem outerInvolutionData_of_concrete {Y A : Type} [Group Y] [Group A] [Finite A]
    (φ : Y ≃* A) {T₀ J : Subgroup A} (hT₀ : IsSylowTwoOf T₀ ⊤) (hJ : J.Normal)
    (hJi : J.index = 2) (hdata : OuterInvolutionData T₀ J) {T N : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hN : ⁅N, N⁆ = N) : OuterInvolutionData T N := by
  obtain ⟨c, -, hc⟩ := hT₀.exists_conj (isSylowTwoOf_top_map_of_mulEquiv φ hT)
  have hJc : J.map (MulAut.conj c).toMonoidHom = J := Subgroup.normal_iff_map_conj_eq.mp hJ c
  have h1 : OuterInvolutionData (T.map φ.toMonoidHom) J := by
    have h := OuterInvolutionData.map (MulAut.conj c) hdata
    rwa [← hc, hJc] at h
  have hNJ : N.map φ.toMonoidHom ≤ J := by
    refine le_of_commutator_eq_self_of_index_two hJi ?_
    rw [← Subgroup.map_commutator, hN]
  have h2 := OuterInvolutionData.map φ.symm (OuterInvolutionData.mono h1 hNJ)
  rwa [map_map_symm_of_mulEquiv, map_map_symm_of_mulEquiv] at h2

end S1421QA17

end CFSG.Quasithin
