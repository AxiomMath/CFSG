module

public import CFSG.Quasithin.AppendixH.H14.H142Arr
public import CFSG.Quasithin.AppendixH.H14.H142StdDefs
public import CFSG.Quasithin.AppendixH.Common.Sextet

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.AppH CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise

@[expose] def uTets : List ℕ := [2101251, 66116, 525336, 4227232]

@[expose] def uArrs : List (Array ℕ) :=
  [#[17, 23, 15, 3, 4, 9, 7, 6, 8, 5, 10, 11, 18, 21, 14, 2, 22, 0, 12, 19, 20, 13, 16, 1],
    #[9, 16, 18, 19, 4, 0, 13, 21, 8, 17, 10, 11, 2, 7, 20, 12, 23, 5, 15, 3, 14, 6, 1, 22],
    #[4, 3, 12, 13, 23, 7, 1, 22, 8, 21, 18, 14, 10, 2, 11, 5, 0, 16, 6, 17, 20, 19, 15, 9],
    #[5, 22, 12, 19, 4, 17, 21, 13, 8, 0, 10, 11, 15, 6, 20, 18, 1, 9, 2, 3, 14, 7, 23, 16]]

theorem uArrs_ok : ∀ j < 4, inAutOK uArrs[j]! = true ∧ (uArrs[j]!)[8]! = 8 ∧
    (∀ m ∈ qMasks, permM uArrs[j]! m ∈ qMasks) ∧ permM uArrs[j]! uTets[j]! = 8790016 := by
  decide +kernel

theorem stdB'_eq : stdB' = maskSetOf 8790016 := by
  decide

theorem stdS_eq_insert : stdS = insert stdB stdQ := by
  decide

theorem exists_stab_of_uTet (j : ℕ) (hj : j < 4) (m : ℕ) (hm : m = uTets[j]!) :
    ∃ u ∈ M24g, u 8 = 8 ∧ u • stdB = stdB ∧ u • stdS = stdS ∧
      u • maskSetOf m = stdB' := by
  obtain ⟨hok, h8, hq, hperm⟩ := uArrs_ok j hj
  have harr : HasArr (permOfArrD uArrs[j]!) uArrs[j]! := hasArr_permOfArrD hok
  have hQ : permOfArrD uArrs[j]! • stdQ = stdQ := smul_stdQ_of_arr harr hq
  refine ⟨permOfArrD uArrs[j]!, permOfArrD_mem_M24g hok, ?_, ?_, ?_, ?_⟩
  · exact Fin.ext ((harr 8).trans h8)
  · exact smul_stdB_of_stdQ hQ
  · simp only [stdS_eq_insert, Finset.smul_finset_insert, smul_stdB_of_stdQ hQ, hQ]
  · rw [smul_maskSetOf harr, hm, hperm]
    exact stdB'_eq.symm

theorem exists_stab_swap_tetrad : ∀ T ∈ stdQ, ∃ u ∈ M24g, u 8 = 8 ∧ u • stdB = stdB ∧
    u • stdS = stdS ∧ u • T = stdB' := by
  intro T hT
  rw [stdQ_eq, List.mem_toFinset, List.mem_map] at hT
  obtain ⟨m, hm, hmT⟩ := hT
  rw [← hmT]
  simp only [qMasks, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm
  · subst hm
    exact exists_stab_of_uTet 0 (by norm_num) 2101251 rfl
  · subst hm
    exact exists_stab_of_uTet 1 (by norm_num) 66116 rfl
  · subst hm
    exact exists_stab_of_uTet 2 (by norm_num) 525336 rfl
  · subst hm
    exact exists_stab_of_uTet 3 (by norm_num) 4227232 rfl
  · subst hm
    refine ⟨1, M24g.one_mem, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp
    · simp
    · rw [one_smul]
      exact stdB'_eq.symm

theorem exists_std_conj {S : Finset (Finset (Fin 24))}
    {B B' : Finset (Fin 24)} {a : Fin 24} (hS : IsSextet S) (hB : B ∈ S) (hB' : B' ∈ S)
    (hBB' : B ≠ B') (ha : a ∈ B) :
    ∃ c ∈ M24g, c a = 8 ∧ c • B = stdB ∧ c • B' = stdB' ∧ c • S = stdS := by
  have hB4 : B.card = 4 := hS.2.1 B hB
  have hcard3 : (B.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, hB4]
  obtain ⟨x, y, z, hxy, hxz, hyz, herase⟩ := Finset.card_eq_three.mp hcard3
  have hax : a ≠ x := (Finset.mem_erase.mp (by rw [herase]; simp)).1.symm
  have hay : a ≠ y := (Finset.mem_erase.mp (by rw [herase]; simp)).1.symm
  have haz : a ≠ z := (Finset.mem_erase.mp (by rw [herase]; simp)).1.symm
  obtain ⟨p, hp, hp0, hp1, hp2, hp3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four a x y z hax hay haz hxy hxz hyz
  obtain ⟨q, hq, hq0, hq1, hq2, hq3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four 8 11 14 20 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  set c₀ : S24 := q * p⁻¹ with hc0def
  have hc0_mem : c₀ ∈ M24g := by
    rw [hc0def]
    exact M24g.mul_mem hq (M24g.inv_mem hp)
  have hc0a : c₀ a = 8 := by
    rw [hc0def, Equiv.Perm.mul_apply]
    have h : p⁻¹ a = 0 := by
      refine p.injective ?_
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact hp0.symm
    rw [h, hq0]
  have hc0x : c₀ x = 11 := by
    rw [hc0def, Equiv.Perm.mul_apply]
    have h : p⁻¹ x = 1 := by
      refine p.injective ?_
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact hp1.symm
    rw [h, hq1]
  have hc0y : c₀ y = 14 := by
    rw [hc0def, Equiv.Perm.mul_apply]
    have h : p⁻¹ y = 2 := by
      refine p.injective ?_
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact hp2.symm
    rw [h, hq2]
  have hc0z : c₀ z = 20 := by
    rw [hc0def, Equiv.Perm.mul_apply]
    have h : p⁻¹ z = 3 := by
      refine p.injective ?_
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      exact hp3.symm
    rw [h, hq3]
  have hBeq : B = {a, x, y, z} := by
    rw [← Finset.insert_erase ha, herase]
  have hc0B : c₀ • B = stdB := by
    rw [hBeq]
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
      hc0a, hc0x, hc0y, hc0z, stdB]
  have hc0S_sext : IsSextet (c₀ • S) := isSextet_smul hc0_mem hS
  have hc0B_mem : c₀ • B ∈ c₀ • S := Finset.smul_mem_smul_finset hB
  have hstdB_mem : stdB ∈ stdS := by decide
  have hc0S : c₀ • S = stdS :=
    sextet_eq_of_mem hc0S_sext isSextet_stdS hc0B_mem (by rw [hc0B]; exact hstdB_mem)
  have hc0B'_mem : c₀ • B' ∈ stdS := by
    have hmem : c₀ • B' ∈ c₀ • S := Finset.smul_mem_smul_finset hB'
    rwa [hc0S] at hmem
  have hc0B'_ne : c₀ • B' ≠ stdB := by
    rw [← hc0B]
    intro h
    exact hBB' (smul_left_cancel c₀ h).symm
  have hc0B'_stdQ : c₀ • B' ∈ stdQ := by
    rw [stdQ, Finset.mem_erase]
    exact ⟨hc0B'_ne, hc0B'_mem⟩
  obtain ⟨u, hu, hu8, huB, huS, huB'⟩ := exists_stab_swap_tetrad (c₀ • B') hc0B'_stdQ
  refine ⟨u * c₀, M24g.mul_mem hu hc0_mem, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hc0a, hu8]
  · rw [mul_smul, hc0B, huB]
  · rw [mul_smul, huB']
  · rw [mul_smul, hc0S, huS]

end CFSG.Quasithin.AppendixH.H14
