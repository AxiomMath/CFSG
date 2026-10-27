module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.RankThree.Native
open CFSG.AGLEmbedding.FusD2 CFSG.AGLEmbedding.MaxD2 Certificates.McLFivePairs

private noncomputable abbrev mclPairGens (g : Equiv.Perm (Fin 275)) : List (Equiv.Perm (Fin 275)) :=
  [mclU5, mclV5, g⁻¹ * mclU5 * g, g⁻¹ * mclV5 * g]

theorem mcl_pair_join
    {i : ℕ} (hi : i ≤ 113)
    (h0 : i ≠ 0) (h95 : i ≠ 95) :
    mclR5 ⊔ mclR5.map (MulAut.conj (mclRep5 i)⁻¹).toMonoidHom = mcl275P := by
  obtain ⟨hmapWords, hPairOK, _⟩ := mcl_pairs_check_spec
  obtain ⟨e, he, hei⟩ : ∃ e ∈ pairWords, e.1 = i := by
    have hmem : i ∈ pairWords.map (·.1) := by
      rw [hmapWords]
      simp only [List.mem_filter, List.mem_range]
      exact ⟨by omega, by simp [h0, h95, excIdx]⟩
    exact List.mem_map.1 hmem
  have hOK := hPairOK e he
  dsimp only [pairOK] at hOK
  rw [hei] at hOK
  simp only [Bool.and_eq_true, beq_iff_eq] at hOK
  obtain ⟨⟨⟨hInv, hgens⟩, hwa⟩, hwb⟩ := hOK
  have hrep := rep_pairGens mcl_rep_u mcl_rep_v (mcl_rep_repT i) hInv
  have hle : mcl275P ≤ Subgroup.closure {g | g ∈ mclPairGens (mclRep5 i)} :=
    mcl_le_closure_of_words hrep hgens hwa hwb
  have hEq : mclR5 ⊔ mclR5.map (MulAut.conj (mclRep5 i)⁻¹).toMonoidHom
      = Subgroup.closure {g | g ∈ mclPairGens (mclRep5 i)} := by
    rw [mclR5_eq]
    exact (closure_four_eq_sup mclU5 mclV5 (mclRep5 i)).symm
  have hmapLe : mclR5.map (MulAut.conj (mclRep5 i)⁻¹).toMonoidHom ≤ mcl275P := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mcl275P.mul_mem
      (mcl275P.mul_mem (mcl275P.inv_mem (mclRep5_mem i)) (mclR5_le hx)) (mclRep5_mem i)
  refine le_antisymm ?_ ?_
  · exact sup_le mclR5_le hmapLe
  · rwa [hEq]

private theorem mclBT5_getD_size (hHT : mclHT5.size = 3) {k : ℕ} (hk : k < 3) :
    (mclBT5.getD k #[]).size = (mclBGens5 k).length := by
  have hk' : k < mclHT5.size := by rw [hHT]; exact hk
  have h1 : (mclBT5.getD k #[]).size = mclB0T.size := by
    simp [mclBT5, blockGens, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem hk']
  have h2 : (mclBGens5 k).length = mclB0Gens.length := by
    simp [mclBGens5]
  have h3 : mclB0T.size = 4 := by
    simp [mclB0T, pairGens]
  have h4 : mclB0Gens.length = 4 := by
    simp [mclB0Gens]
  omega

private theorem mclB5_sup_lt
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i < j) :
    mclB5 ⟨i, hi⟩ ⊔ mclB5 ⟨j, hj⟩ = mcl275P := by
  obtain ⟨_, _, _, _, hHT, _, _, _, _, hjoinMap, hjoinOK, _⟩ := mcl_pairs_check_spec
  have hmem : (i, j) ∈ joinIndex := by
    interval_cases i <;> interval_cases j <;> simp_all [joinIndex]
  obtain ⟨e, he, heij⟩ : ∃ e ∈ joinWords, (e.1, e.2.1) = (i, j) := by
    rw [← hjoinMap] at hmem
    exact List.mem_map.1 hmem
  have he1 : e.1 = i := congrArg Prod.fst heij
  have he2 : e.2.1 = j := congrArg Prod.snd heij
  have hOK := hjoinOK e he
  simp only [joinOK] at hOK
  rw [he1, he2] at hOK
  simp only [Bool.and_eq_true, beq_iff_eq] at hOK
  obtain ⟨⟨hgens, hwa⟩, hwb⟩ := hOK
  have hbi : ∀ t, TabRep ((mclBT5.getD i #[]).getD t (idTab 275)) ((mclBGens5 i).getD t 1) :=
    rep_mclBT5 hi
  have hbj : ∀ t, TabRep ((mclBT5.getD j #[]).getD t (idTab 275)) ((mclBGens5 j).getD t 1) :=
    rep_mclBT5 hj
  have hsize : (mclBT5.getD i #[]).size = (mclBGens5 i).length :=
    mclBT5_getD_size hHT hi
  have hrep := rep_append hbi hbj hsize
  have hle : mcl275P ≤ Subgroup.closure {g | g ∈ mclBGens5 i ++ mclBGens5 j} :=
    mcl_le_closure_of_words hrep hgens hwa hwb
  have hUnion : Subgroup.closure {g | g ∈ mclBGens5 i ++ mclBGens5 j}
      = mclB5 ⟨i, hi⟩ ⊔ mclB5 ⟨j, hj⟩ := by
    have hset : {g : Equiv.Perm (Fin 275) | g ∈ mclBGens5 i ++ mclBGens5 j}
        = {g | g ∈ mclBGens5 i} ∪ {g | g ∈ mclBGens5 j} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_append]
    rw [hset, Subgroup.closure_union]
  refine le_antisymm ?_ ?_
  · exact sup_le (mclB5_le ⟨i, hi⟩) (mclB5_le ⟨j, hj⟩)
  · rwa [hUnion] at hle

theorem mclB5_sup
    {k l : Fin 3} (hkl : k ≠ l) :
    mclB5 k ⊔ mclB5 l = mcl275P := by
  have hval : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with h | h
  · exact mclB5_sup_lt k.isLt l.isLt h
  · rw [sup_comm]
    exact mclB5_sup_lt l.isLt k.isLt h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
