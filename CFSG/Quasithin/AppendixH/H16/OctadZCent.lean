module

public import CFSG.Quasithin.AppendixH.H16.OctadTransit
public import CFSG.Quasithin.AppendixH.Common.OctadStd

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

theorem koPerm_one_fix_iff (i : Fin 24) : koPerm 1 i = i ↔ i ∈ octad0 := by
  have h : ∀ i : Fin 24, koPerm 1 i = i ↔ i ∈ octad0 := by decide +kernel
  exact h i

theorem koPerm_one_mem_octStab : koPerm 1 ∈ octStab octad0 :=
  fixO_le_octStab_octad0 ((mem_fixO_iff _).2 ⟨1, rfl⟩)

theorem cent_koOne_le_octStab :
    M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24) ≤ octStab octad0 := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgM, hgC⟩ := hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgC
  rw [mem_octStab_iff]
  refine ⟨hgM, ?_⟩
  ext i
  rw [smul_finset_eq_map, Finset.mem_map_equiv]
  constructor
  · intro hi
    have hfix := (koPerm_one_fix_iff (g.symm i)).2 hi
    have h := congrArg (fun p : S24 => p (g.symm i)) hgC
    simp only [Equiv.Perm.mul_apply] at h
    rw [hfix, Equiv.apply_symm_apply] at h
    exact (koPerm_one_fix_iff i).1 h.symm
  · intro hi
    have hfix := (koPerm_one_fix_iff i).2 hi
    have h := congrArg (fun p : S24 => p (g.symm i)) hgC
    simp only [Equiv.Perm.mul_apply] at h
    rw [Equiv.apply_symm_apply, hfix] at h
    have h2 : koPerm 1 (g.symm i) = g.symm i := by
      have := congrArg g.symm h
      simpa using this
    exact (koPerm_one_fix_iff (g.symm i)).1 h2

private theorem koPerm_one_ne_one : koPerm 1 ≠ (1 : S24) := by
  intro h
  have h8 : ((koPerm 1 (⟨8, by norm_num⟩ : Fin 24) : Fin 24) : ℕ) = 9 := by
    have := koPerm_val 1 (0 : Fin 16)
    simpa using this
  rw [h] at h8
  simp at h8

theorem ncard_conjugatesOf_koOne :
    (conjugatesOf (⟨koPerm 1, koPerm_one_mem_octStab⟩ : ↥(octStab octad0))).ncard = 15 := by
  let g0 : ↥(octStab octad0) := ⟨koPerm 1, koPerm_one_mem_octStab⟩
  change (conjugatesOf g0).ncard = 15
  have hset : (conjugatesOf g0 : Set ↥(octStab octad0)) =
      {x : ↥(octStab octad0) | (x : S24) ∈ fixO ∧ (x : S24) ≠ 1} := by
    ext x
    constructor
    · intro hx
      have hx' : IsConj g0 x := hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx'
      constructor
      · rw [← hc]
        have hN : ((octFix octad0).subgroupOf (octStab octad0)).Normal := normal_octFix octad0
        have hg0 : g0 ∈ (octFix octad0).subgroupOf (octStab octad0) := by
          rw [Subgroup.mem_subgroupOf, octFix_octad0]
          exact (mem_fixO_iff _).2 ⟨1, rfl⟩
        have hconj := hN.conj_mem g0 hg0 c
        rw [Subgroup.mem_subgroupOf, octFix_octad0] at hconj
        exact hconj
      · intro hx1
        apply koPerm_one_ne_one
        have hone : g0 = 1 := by
          have h1 : c * g0 * c⁻¹ = (1 : ↥(octStab octad0)) := by
            apply Subtype.ext
            rw [hc, hx1]
            rfl
          calc g0 = c⁻¹ * (c * g0 * c⁻¹) * c := by group
            _ = c⁻¹ * (1 : ↥(octStab octad0)) * c := by rw [h1]
            _ = 1 := by group
        simpa [g0] using congrArg Subtype.val hone
    · intro hx
      obtain ⟨hxF, hx1⟩ := hx
      obtain ⟨t, ht⟩ := (mem_fixO_iff (x : S24)).1 hxF
      have ht0 : t ≠ 0 := by
        intro h0
        apply hx1
        rw [ht, h0, koPerm_zero]
      obtain ⟨m, hm, hmc⟩ := exists_octStab_conj_koPerm t ht0
      have hconj : (⟨m, hm⟩ : ↥(octStab octad0)) * g0 * (⟨m, hm⟩ : ↥(octStab octad0))⁻¹ = x := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, g0]
        rw [hmc, ht]
      exact isConj_iff.mpr ⟨⟨m, hm⟩, hconj⟩
  rw [hset]
  have himg : (Subtype.val '' {x : ↥(octStab octad0) | (x : S24) ∈ fixO ∧ (x : S24) ≠ 1})
      = {y : S24 | y ∈ fixO ∧ y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, fixO_le_octStab_octad0 hy.1⟩, hy, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  have hT : ({y : S24 | y ∈ fixO ∧ y ≠ 1} : Set S24) = (fixO : Set S24) \ {1} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, by simpa using hy.2⟩
    · intro hy
      exact ⟨hy.1, by simpa using hy.2⟩
  rw [hT, Set.ncard_diff_singleton_of_mem (show (1 : S24) ∈ (fixO : Set S24) from fixO.one_mem)]
  have hcard_fixO : (fixO : Set S24).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card ↥fixO = 16
    rw [← octFix_octad0, card_octFix isOctad_octad0]
  rw [hcard_fixO]

theorem card_cent_koOne :
    Nat.card ↥(M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)) = 21504 := by
  let g0 : ↥(octStab octad0) := ⟨koPerm 1, koPerm_one_mem_octStab⟩
  have hclass : (conjugatesOf g0).ncard = 15 := by
    simpa [g0] using ncard_conjugatesOf_koOne
  have hidx : (Subgroup.centralizer ({g0} : Set ↥(octStab octad0))).index = 15 := by
    rw [Subgroup.index_centralizer_eq_ncard, hclass]
  have hcard : Nat.card ↥(Subgroup.centralizer ({g0} : Set ↥(octStab octad0))) = 21504 := by
    have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({g0} : Set ↥(octStab octad0)))
    rw [hidx, card_octStab_octad0] at hmul
    omega
  have hmap : M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)
      = (Subgroup.centralizer ({g0} : Set ↥(octStab octad0))).map (octStab octad0).subtype := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyM, hyC⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC
      have hyO : y ∈ octStab octad0 :=
        cent_koOne_le_octStab (Subgroup.mem_inf.mpr
          ⟨hyM, Subgroup.mem_centralizer_singleton_iff.mpr hyC⟩)
      rw [Subgroup.mem_map]
      refine ⟨⟨y, hyO⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa [g0] using hyC
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [← hxy]
        exact x.2.1
      · rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_singleton_iff] at hx
        rw [← hxy]
        exact congrArg Subtype.val hx
  rw [hmap, Subgroup.card_map_of_injective (octStab octad0).subtype_injective]
  exact hcard

end CFSG.ASVolI.H16
