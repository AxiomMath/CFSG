module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

private def pa : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * Equiv.swap 0 2
private def pb : Equiv.Perm (Fin 10) := Equiv.swap 3 4 * Equiv.swap 3 5
private def pc : Equiv.Perm (Fin 10) := Equiv.swap 6 7 * Equiv.swap 6 8
private def qa : Equiv.Perm (Fin 10) := Equiv.swap 3 0 * Equiv.swap 3 6
private def qb : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * Equiv.swap 4 7
private def qc : Equiv.Perm (Fin 10) := Equiv.swap 5 2 * Equiv.swap 5 8
private def py : Equiv.Perm (Fin 10) := qa * qb * qc

private lemma pa_cube : pa ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private lemma pb_cube : pb ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private lemma pc_cube : pc ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private lemma py_cube : py ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private lemma pa_mul_pb : pa * pb = pb * pa := by
  ext i
  fin_cases i <;> decide

private lemma pa_mul_pc : pa * pc = pc * pa := by
  ext i
  fin_cases i <;> decide

private lemma pb_mul_pc : pb * pc = pc * pb := by
  ext i
  fin_cases i <;> decide

private lemma py_mul_pa : py * pa = pb * py := by
  ext i
  fin_cases i <;> decide

private lemma py_mul_pb : py * pb = pc * py := by
  ext i
  fin_cases i <;> decide

private lemma py_mul_pc : py * pc = pa * py := by
  ext i
  fin_cases i <;> decide

private lemma pa_mul_py_ne : pa * py ≠ py * pa := by
  intro h
  have h0 : (pa * py) 0 = (py * pa) 0 := congrArg (fun σ : Equiv.Perm (Fin 10) => σ 0) h
  exact absurd h0 (by decide)

private lemma pa_isThreeCycle : Equiv.Perm.IsThreeCycle pa := by
  change Equiv.Perm.IsThreeCycle (Equiv.swap 0 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 10))
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma pa_mem_alt : pa ∈ alternatingGroup (Fin 10) :=
  Equiv.Perm.IsThreeCycle.mem_alternatingGroup pa_isThreeCycle

private lemma qa_isThreeCycle : Equiv.Perm.IsThreeCycle qa := by
  change Equiv.Perm.IsThreeCycle (Equiv.swap 3 0 * Equiv.swap 3 6 : Equiv.Perm (Fin 10))
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma qb_isThreeCycle : Equiv.Perm.IsThreeCycle qb := by
  change Equiv.Perm.IsThreeCycle (Equiv.swap 4 1 * Equiv.swap 4 7 : Equiv.Perm (Fin 10))
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma qc_isThreeCycle : Equiv.Perm.IsThreeCycle qc := by
  change Equiv.Perm.IsThreeCycle (Equiv.swap 5 2 * Equiv.swap 5 8 : Equiv.Perm (Fin 10))
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma py_mem_alt : py ∈ alternatingGroup (Fin 10) := by
  change qa * qb * qc ∈ alternatingGroup (Fin 10)
  exact mul_mem (mul_mem (Equiv.Perm.IsThreeCycle.mem_alternatingGroup qa_isThreeCycle)
    (Equiv.Perm.IsThreeCycle.mem_alternatingGroup qb_isThreeCycle))
    (Equiv.Perm.IsThreeCycle.mem_alternatingGroup qc_isThreeCycle)

private lemma isPGroup_zpowers_of_cube {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers u) := by
  refine IsPGroup.of_card_dvd_pow (p := 3) (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_dvd_iff_pow_eq_one.mpr hu

private lemma zpowers_le_normalizer_of_mul_eq {G : Type*} [Group G] {u v : G}
    (h : u * v = v * u) :
    Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  rw [Subgroup.zpowers_le]
  apply (Subgroup.mem_normalizer_iff_map_conj_eq (H := Subgroup.zpowers v) (g := u)).mpr
  rw [MonoidHom.map_zpowers]
  congr 1
  change u * v * u⁻¹ = v
  calc u * v * u⁻¹ = v * u * u⁻¹ := by rw [h]
    _ = v := by rw [mul_assoc, mul_inv_cancel, mul_one]

private def subA : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.zpowers pa
private def subB : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.zpowers pb
private def subC : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.zpowers pc
private def subY : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.zpowers py
private def subN : Subgroup (Equiv.Perm (Fin 10)) := subA ⊔ subB ⊔ subC
private def subP : Subgroup (Equiv.Perm (Fin 10)) := subY ⊔ subN

private lemma isPGroup_subA : IsPGroup 3 subA := by
  change IsPGroup 3 (Subgroup.zpowers pa)
  exact isPGroup_zpowers_of_cube pa_cube

private lemma isPGroup_subB : IsPGroup 3 subB := by
  change IsPGroup 3 (Subgroup.zpowers pb)
  exact isPGroup_zpowers_of_cube pb_cube

private lemma isPGroup_subC : IsPGroup 3 subC := by
  change IsPGroup 3 (Subgroup.zpowers pc)
  exact isPGroup_zpowers_of_cube pc_cube

private lemma isPGroup_subY : IsPGroup 3 subY := by
  change IsPGroup 3 (Subgroup.zpowers py)
  exact isPGroup_zpowers_of_cube py_cube

private lemma subA_le_subB_normalizer : subA ≤ Subgroup.normalizer (subB : Set _) := by
  change Subgroup.zpowers pa ≤ Subgroup.normalizer (Subgroup.zpowers pb : Set _)
  exact zpowers_le_normalizer_of_mul_eq pa_mul_pb

private lemma subA_le_subC_normalizer : subA ≤ Subgroup.normalizer (subC : Set _) := by
  change Subgroup.zpowers pa ≤ Subgroup.normalizer (Subgroup.zpowers pc : Set _)
  exact zpowers_le_normalizer_of_mul_eq pa_mul_pc

private lemma subB_le_subC_normalizer : subB ≤ Subgroup.normalizer (subC : Set _) := by
  change Subgroup.zpowers pb ≤ Subgroup.normalizer (Subgroup.zpowers pc : Set _)
  exact zpowers_le_normalizer_of_mul_eq pb_mul_pc

private lemma subAB_le_subC_normalizer : subA ⊔ subB ≤ Subgroup.normalizer (subC : Set _) :=
  sup_le subA_le_subC_normalizer subB_le_subC_normalizer

private lemma isPGroup_subAB : IsPGroup 3 ↥(subA ⊔ subB) :=
  IsPGroup.to_sup_of_normal_right' isPGroup_subA isPGroup_subB subA_le_subB_normalizer

private lemma isPGroup_subN : IsPGroup 3 subN := by
  change IsPGroup 3 ↥(subA ⊔ subB ⊔ subC)
  exact IsPGroup.to_sup_of_normal_right' isPGroup_subAB isPGroup_subC subAB_le_subC_normalizer

private lemma map_conj_subA : subA.map (MulAut.conj py) = subB := by
  change (Subgroup.zpowers pa).map (MulAut.conj py) = Subgroup.zpowers pb
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (py * pa * py⁻¹) = Subgroup.zpowers pb
  rw [py_mul_pa, mul_assoc, mul_inv_cancel, mul_one]

private lemma map_conj_subB : subB.map (MulAut.conj py) = subC := by
  change (Subgroup.zpowers pb).map (MulAut.conj py) = Subgroup.zpowers pc
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (py * pb * py⁻¹) = Subgroup.zpowers pc
  rw [py_mul_pb, mul_assoc, mul_inv_cancel, mul_one]

private lemma map_conj_subC : subC.map (MulAut.conj py) = subA := by
  change (Subgroup.zpowers pc).map (MulAut.conj py) = Subgroup.zpowers pa
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (py * pc * py⁻¹) = Subgroup.zpowers pa
  rw [py_mul_pc, mul_assoc, mul_inv_cancel, mul_one]

private lemma map_conj_subN : subN.map (MulAut.conj py) = subN := by
  change (subA ⊔ subB ⊔ subC).map (MulAut.conj py) = subA ⊔ subB ⊔ subC
  rw [Subgroup.map_sup, Subgroup.map_sup, map_conj_subA, map_conj_subB, map_conj_subC]
  ac_rfl

private lemma subY_le_subN_normalizer : subY ≤ Subgroup.normalizer (subN : Set _) := by
  change Subgroup.zpowers py ≤ Subgroup.normalizer (subN : Set _)
  rw [Subgroup.zpowers_le]
  apply (Subgroup.mem_normalizer_iff_map_conj_eq (H := subN) (g := py)).mpr
  exact map_conj_subN

private lemma isPGroup_subP : IsPGroup 3 subP := by
  change IsPGroup 3 ↥(subY ⊔ subN)
  exact IsPGroup.to_sup_of_normal_right' isPGroup_subY isPGroup_subN subY_le_subN_normalizer

private lemma subA_le_subP : subA ≤ subP :=
  le_trans (le_trans le_sup_left le_sup_left) le_sup_right

private lemma subY_le_subP : subY ≤ subP := le_sup_left

theorem exists_noncommute_three_of_isAlt_ten {X : Type} [Group X] (hX : IsAlt X 10) :
    ∃ P : Subgroup X, IsPGroup 3 P ∧
      ∃ x ∈ P, ∃ y ∈ P, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨e⟩ := hX
  have hPsub : IsPGroup 3 (subP.subgroupOf (alternatingGroup (Fin 10))) := by
    rw [← Subgroup.comap_subtype subP (alternatingGroup (Fin 10))]
    exact isPGroup_subP.comap_subtype
  refine ⟨(subP.subgroupOf (alternatingGroup (Fin 10))).map e.symm.toMonoidHom,
    hPsub.map e.symm.toMonoidHom, ?_⟩
  refine ⟨e.symm ⟨pa, pa_mem_alt⟩, ?_, e.symm ⟨py, py_mem_alt⟩, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_map.mpr ⟨⟨pa, pa_mem_alt⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (subA_le_subP (Subgroup.mem_zpowers pa))
  · refine Subgroup.mem_map.mpr ⟨⟨py, py_mem_alt⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (subY_le_subP (Subgroup.mem_zpowers py))
  · have h3 : (⟨pa, pa_mem_alt⟩ : alternatingGroup (Fin 10)) ^ 3 = 1 := by
      apply Subtype.ext
      change pa ^ 3 = 1
      exact pa_cube
    rw [← map_pow e.symm, h3, map_one]
  · have h3 : (⟨py, py_mem_alt⟩ : alternatingGroup (Fin 10)) ^ 3 = 1 := by
      apply Subtype.ext
      change py ^ 3 = 1
      exact py_cube
    rw [← map_pow e.symm, h3, map_one]
  · intro h
    exact pa_mul_py_ne (by simpa using congrArg e h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
