module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCartan
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroFourJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

private theorem ggCoxeterMatrixA_M_le_three (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (CoxeterMatrix.A n).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
  split_ifs <;> omega

theorem GGCaseZeroData.join_type (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    (∃ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M ∧ GGSimplyLacedConnected M ∧
        ∃ f : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
          ∀ i, GGIsReflection p ((f (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∨
      (∃ (m : ℕ), 2 ≤ m ∧ ∃ f : (CoxeterMatrix.B m).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
          ∀ i, GGIsReflection p
            ((f ((CoxeterMatrix.B m).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∨
      ∃ f : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
          ∀ i, GGIsReflection p
            ((f (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
  obtain ⟨-, hW, -⟩ := h.cfg.2.2.2
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have hM0 := hM
  rcases hM with ⟨n, eA, _, hcase⟩ | ⟨e6, hE6⟩ | ⟨e7, hE7⟩ | ⟨e8, hE8⟩ |
    ⟨eF4, hF4⟩ | ⟨eG2, hG2⟩
  · rcases hcase with hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩
    ·
      left
      refine ⟨ι, M, hM0, ?_, f, hf⟩
      rw [hA]
      refine ggSimplyLacedConnected_of_weyl ?_ ?_
      · rwa [hA] at hM0
      · intro i j hij
        rw [CoxeterMatrix.reindex_apply]
        exact ggCoxeterMatrixA_M_le_three n (eA.symm i) (eA.symm j)
          (fun h' => hij (eA.symm.injective h'))
    ·
      right; left
      subst M
      refine ⟨n, hn2, ((CoxeterMatrix.B n).reindexGroupEquiv eA).symm.trans f, ?_⟩
      intro i
      rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
      exact hf (eA i)
    ·
      left
      refine ⟨ι, M, hM0, ?_, f, hf⟩
      rw [hD]
      refine ggSimplyLacedConnected_of_weyl ?_ ?_
      · rwa [hD] at hM0
      · exact GGIsWeylMatrixAD.le_three (Or.inr ⟨n, eA, hn4, rfl⟩)
  ·
    left
    refine ⟨ι, M, hM0, ?_, f, hf⟩
    rw [hE6]
    refine ggSimplyLacedConnected_of_weyl ?_ ?_
    · rwa [hE6] at hM0
    · exact GGIsWeylMatrixE.le_three (Or.inl ⟨e6, rfl⟩)
  ·
    left
    refine ⟨ι, M, hM0, ?_, f, hf⟩
    rw [hE7]
    refine ggSimplyLacedConnected_of_weyl ?_ ?_
    · rwa [hE7] at hM0
    · exact GGIsWeylMatrixE.le_three (Or.inr (Or.inl ⟨e7, rfl⟩))
  ·
    left
    refine ⟨ι, M, hM0, ?_, f, hf⟩
    rw [hE8]
    refine ggSimplyLacedConnected_of_weyl ?_ ?_
    · rwa [hE8] at hM0
    · exact GGIsWeylMatrixE.le_three (Or.inr (Or.inr ⟨e8, rfl⟩))
  ·
    right; right
    subst M
    refine ⟨(CoxeterMatrix.F₄.reindexGroupEquiv eF4).symm.trans f, ?_⟩
    intro i
    rw [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
    exact hf (eF4 i)
  ·
    exfalso
    obtain ⟨ιL, hFinL, ML, hML, hAL⟩ := h.frame
    exact @ggRM_not_G2_of_le G _ _ p Bs ι M ιL hFinL ML hML
      (ggAutomizer L Bs) (ggAutomizerJoin L Bs 𝒦) hAL
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)) f ⟨eG2, hG2⟩

theorem GGCaseZeroData.witness (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    GGSecFiveInfWitness p B Bs x L D J := by
  obtain ⟨hp, hp2, hBs, hNT⟩ := h.basic
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  let : AddCommGroup V := iadd
  let : Module (ZMod p) V := imod
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have hind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := fun a ha =>
    ggRM_ainf_le_induced (h.join_le_ainf ha)
  apply h.witness_of_refl_mem
  intro y K hK t htK ht
  have htInf : t ∈ ggAInf p B Bs x L D J := ggAutomizer_le_ggAInf_of_nbr hK htK
  by_cases hEq : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs
  · rw [hEq]
    exact h.nbr_le_of_join_eq hEq y K hK htK
  rcases h.join_type with ⟨ι, M, hM, hSL, f, hf⟩ | ⟨m, hm, f, hf⟩ | ⟨f, hf⟩
  ·
    exact absurd (le_antisymm (h.le_AL_of_simplyLaced
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)) h.join_le_ainf hM hSL f hf)
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))) hEq
  ·
    obtain ⟨e, φ, hd, hA⟩ := ggCZ_coordsB hp2 hNT hm hind f hf ιV
    obtain ⟨hm3, hF⟩ := h.frameD_of_B hm ιV hd hA hEq
    have hsub := ggCZ_subset_ggCZWB hd
    have hmem : ggLin (p := p) ιV t ∈ ggCZRD e φ ∪ ggCZS e φ →
        t ∈ ggAutomizerJoin L Bs 𝒦 := by
      intro hRS
      have hW := hsub hRS
      rw [← hA] at hW
      obtain ⟨a, ha, hat⟩ := hW
      rw [← ggLin_injective (p := p) ιV hat]
      exact ha
    rcases h.refl_shape hm3 ιV hF t htInf ht with hR | hS | ⟨rfl, hH⟩
    · exact hmem (Or.inl hR)
    · exact hmem (Or.inr hS)
    · exact (h.false_of_B4_half ιV hd hA hEq hK htK ht hH).elim
  ·
    obtain ⟨e, φ, hd, -, hA⟩ := ggCZ_coordsF4 hp2 hNT hind f hf ιV
    obtain ⟨e', φ', hF, hset⟩ := h.frameD_of_F4 ιV hd hA hEq
    have hsub := ggCZ_subset_ggCZWF4 hp2 hd
    have hall : ggLin (p := p) ιV t ∈ ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ := by
      rw [← hset]
      rcases h.refl_shape (by norm_num) ιV hF t htInf ht with hR | hS | ⟨-, hH⟩
      · exact Or.inl (Or.inl hR)
      · exact Or.inl (Or.inr hS)
      · exact Or.inr hH
    have hW := hsub hall
    rw [← hA] at hW
    obtain ⟨a, ha, hat⟩ := hW
    rw [← ggLin_injective (p := p) ιV hat]
    exact ha

theorem ggSecFiveCaseZeroInput_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hFix : GGSecFiveFixInput)
    (hRootGenL : GGSecFiveRootGenLInput) : GGSecFiveCaseZeroInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ hcfg hsplit hxBs hfix _ =>
    (ggCZ_data_of_inputs hL hP hFix hRootGenL hcfg hsplit hxBs hfix).witness

end

end CFSG.StandardType

end
