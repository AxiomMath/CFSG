module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

private lemma spUCited_flag_two_eq (hr : 2 ≤ r) {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ flag r K 2) :
    v = v (Sum.inl (⟨0, by omega⟩ : Fin r)) •
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) +
        v (Sum.inl (⟨1, by omega⟩ : Fin r)) •
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) := by
  obtain ⟨hv1, hv2⟩ := mem_isoFlag.mp ((mem_flag_of_le (i := 2) hr).mp hv)
  funext y
  rcases y with j | j
  · by_cases hj0 : (j : ℕ) = 0
    · have hje : j = (⟨0, by omega⟩ : Fin r) := Fin.ext hj0
      rw [hje]
      simp
    · by_cases hj1 : (j : ℕ) = 1
      · have hje : j = (⟨1, by omega⟩ : Fin r) := Fin.ext hj1
        rw [hje]
        simp
      · have hj2 : 2 ≤ (j : ℕ) := by omega
        have hz := hv2 j hj2
        have h0 : j ≠ (⟨0, by omega⟩ : Fin r) := fun h => hj0 (by rw [h])
        have h1 : j ≠ (⟨1, by omega⟩ : Fin r) := fun h => hj1 (by rw [h])
        simp [Pi.single_apply, h0, h1, hz]
  · have hz := hv1 j
    simp [Pi.single_apply, hz]

private lemma spUCited_spEnd_mem_flag {g : ↥(StatedSp r K)} {i : ℕ}
    (hg : g ∈ stabilizer r K (flag r K i)) {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ flag r K i) : spEnd g v ∈ flag r K i := by
  rw [mem_stabilizer] at hg
  rw [← hg]
  exact ⟨v, hv, by rw [Matrix.mulVecLin_apply, spEnd_apply]⟩

theorem spUCited_mem_unipotent_of_sub_mem {y : ↥(StatedSp r K)} (hy : y ∈ borelSubgroup r K)
    (h : ∀ i, 1 ≤ i → i ≤ r → ∀ v ∈ flag r K i, spEnd y v - v ∈ flag r K (i - 1)) :
    y ∈ unipotent r K := by
  obtain ⟨A, C, hA, hdet, hC, hg⟩ := mem_borelSubgroup_iff.mp hy
  have hdiag : ∀ j : Fin r, A j j = 1 := by
    intro j
    have hv : (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) ∈ flag r K (j + 1) :=
      (mem_flag_of_le (i := j + 1) (Nat.succ_le_of_lt j.2)).mpr (single_mem_isoFlag j)
    have hmem := h (j + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt j.2) _ hv
    have hcoord := mem_flag_iff.mp hmem (Sum.inl j) (by rw [flagOrder_inl]; omega)
    have hcalc : (spEnd y (Pi.single (Sum.inl j) (1 : K)) -
          (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) (Sum.inl j) = A j j - 1 := by
      rw [Pi.sub_apply, spEnd_apply, hg, Matrix.mulVec_single_one, Matrix.col_apply]
      simp [blockMat, Matrix.fromBlocks_apply₁₁, Pi.single_apply]
    rw [hcalc] at hcoord
    exact sub_eq_zero.mp hcoord
  exact mem_unipotent.mpr ⟨A, C, ⟨hA, hdiag⟩, hC, hg⟩

theorem spUCited_mem_inf_normalizer_iff (hr : 2 ≤ r) (x : ↥(StatedSp r K)) :
    x ∈ unipotent r K ⊓ Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K)) ↔
      x ∈ unipotent r K ∧ spEnd x (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) := by
  constructor
  · rintro ⟨hxu, hxn⟩
    refine ⟨hxu, ?_⟩
    obtain ⟨c, hc0, hc⟩ :=
      (spUCited_mem_normalizer_root_iff (K := K) (i := ⟨1, by omega⟩) x).mp hxn
    obtain ⟨c', hc'⟩ := spUCited_unipotent_apply_one (K := K) hr hxu
    have hcoef := congrFun (hc.symm.trans hc') (Sum.inl (⟨1, by omega⟩ : Fin r))
    have hc1 : c = 1 := by simpa using hcoef
    rw [hc1, one_smul] at hc
    exact hc
  · rintro ⟨hxu, hxe⟩
    refine ⟨hxu, ?_⟩
    change x ∈ Subgroup.normalizer
      (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))
    rw [spUCited_mem_normalizer_root_iff]
    exact ⟨1, one_ne_zero, by simpa using hxe⟩

theorem spUCited_conj_mem_inf_normalizer (hr : 2 ≤ r) {g : ↥(StatedSp r K)}
    (hg : g ∈ spUCitedPar r K) {x : ↥(StatedSp r K)}
    (hx : x ∈ unipotent r K ⊓
      Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))) :
    g * x * g⁻¹ ∈ unipotent r K ⊓
      Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K)) := by
  obtain ⟨hxu, hxe⟩ := (spUCited_mem_inf_normalizer_iff (K := K) hr x).mp hx
  have hg' : g ∈ flagStabilizer r K (Set.Icc 2 r) := hg
  have hginv : g⁻¹ ∈ flagStabilizer r K (Set.Icc 2 r) := (spUCitedPar r K).inv_mem hg
  have hxpar : x ∈ flagStabilizer r K (Set.Icc 2 r) :=
    borelSubgroup_le_flagStabilizer (K := K) (I := Set.Icc 2 r) (fun i hi => hi.2)
      (unipotent_le_borelSubgroup hxu)
  set y : ↥(StatedSp r K) := g * x * g⁻¹ with hydef
  change y ∈ unipotent r K ⊓
    Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))
  have hydecomp : spEnd y = spEnd g * spEnd x * spEnd g⁻¹ := by
    rw [hydef, spEnd_mul, spEnd_mul]
  have hxe1 : spEnd x (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) =
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) := by
    have hv : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) ∈
        flag r K 1 :=
      (mem_flag_of_le (i := 1) (by omega)).mpr (single_mem_isoFlag ⟨0, by omega⟩)
    have h := unipotent_sub_mulVec_mem_flag hxu (i := 0) hv
    rw [flag_zero, Submodule.mem_bot, sub_eq_zero] at h
    simpa [spEnd_apply] using h
  have hfixx : ∀ v ∈ flag r K 2, spEnd x v = v := by
    intro v hv
    have hd := spUCited_flag_two_eq (K := K) hr hv
    rw [hd]
    simp only [map_add, map_smul]
    rw [hxe1, hxe]
  have hfix2 : ∀ v ∈ flag r K 2, spEnd y v = v := by
    intro v hv
    have hw : spEnd g⁻¹ v ∈ flag r K 2 :=
      spUCited_spEnd_mem_flag (mem_flagStabilizer.mp hginv 2 (by
        exact ⟨le_rfl, hr⟩)) hv
    have hxw : spEnd x (spEnd g⁻¹ v) = spEnd g⁻¹ v := hfixx _ hw
    have hgg : spEnd g (spEnd g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one]
      rfl
    calc spEnd y v = spEnd g (spEnd x (spEnd g⁻¹ v)) := by
          rw [hydecomp]
          rfl
      _ = spEnd g (spEnd g⁻¹ v) := by rw [hxw]
      _ = v := hgg
  have hyinv_fix2 : ∀ v ∈ flag r K 2, spEnd y⁻¹ v = v := by
    intro v hv
    have h1 : spEnd y⁻¹ (spEnd y v) = v := by
      rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one]
      rfl
    rwa [hfix2 v hv] at h1
  have hstab1 : y ∈ stabilizer r K (flag r K 1) := by
    refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) fun v hv => ?_
    · have hv2 : v ∈ flag r K 2 := flag_mono (by norm_num) hv
      rw [← spEnd_apply, hfix2 v hv2]
      exact hv
    · have hv2 : v ∈ flag r K 2 := flag_mono (by norm_num) hv
      rw [← spEnd_apply, hyinv_fix2 v hv2]
      exact hv
  have hstab : ∀ i, 2 ≤ i → i ≤ r → y ∈ stabilizer r K (flag r K i) := by
    intro i hi2 hir
    have hiI : i ∈ Set.Icc 2 r := ⟨hi2, hir⟩
    exact (stabilizer r K (flag r K i)).mul_mem
      ((stabilizer r K (flag r K i)).mul_mem
        (mem_flagStabilizer.mp hg' i hiI) (mem_flagStabilizer.mp hxpar i hiI))
      (mem_flagStabilizer.mp hginv i hiI)
  have hyB : y ∈ borelSubgroup r K := by
    refine mem_borelSubgroup.mpr fun i hi1 hir => ?_
    rcases eq_or_lt_of_le hi1 with rfl | hi2
    · exact hstab1
    · exact hstab i (by omega) hir
  have hmem : ∀ i, 1 ≤ i → i ≤ r → ∀ v ∈ flag r K i,
      spEnd y v - v ∈ flag r K (i - 1) := by
    intro i hi1 hir v hv
    rcases eq_or_lt_of_le hi1 with rfl | hi2
    · have hv2 : v ∈ flag r K 2 := flag_mono (by norm_num) hv
      rw [show 1 - 1 = 0 by norm_num, flag_zero, Submodule.mem_bot, sub_eq_zero]
      exact hfix2 v hv2
    · rcases (show i = 2 ∨ 3 ≤ i by omega) with rfl | hi3
      · rw [sub_eq_zero.mpr (hfix2 v hv)]
        exact Submodule.zero_mem _
      · have hw : spEnd g⁻¹ v ∈ flag r K i :=
          spUCited_spEnd_mem_flag (mem_flagStabilizer.mp hginv i ⟨by omega, hir⟩) hv
        have hxw : spEnd x (spEnd g⁻¹ v) - spEnd g⁻¹ v ∈ flag r K (i - 1) := by
          have h := unipotent_sub_mulVec_mem_flag hxu (i := i - 1) (v := spEnd g⁻¹ v) (by
            rw [show i - 1 + 1 = i by omega]
            exact hw)
          simpa [spEnd_apply] using h
        have hconv : spEnd g (spEnd x (spEnd g⁻¹ v) - spEnd g⁻¹ v) ∈ flag r K (i - 1) :=
          spUCited_spEnd_mem_flag
            (mem_flagStabilizer.mp hg' (i - 1) ⟨by omega, by omega⟩) hxw
        have hgg : spEnd g (spEnd g⁻¹ v) = v := by
          rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one]
          rfl
        have heq : spEnd y v - v =
            spEnd g (spEnd x (spEnd g⁻¹ v) - spEnd g⁻¹ v) := by
          rw [hydecomp, Module.End.mul_apply, Module.End.mul_apply, map_sub, hgg]
        rw [heq]
        exact hconv
  have hyU : y ∈ unipotent r K := spUCited_mem_unipotent_of_sub_mem hyB hmem
  have hye2 : spEnd y (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) =
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) := by
    refine hfix2 _ ?_
    exact (mem_flag_of_le (i := 2) hr).mpr (single_mem_isoFlag ⟨1, by omega⟩)
  exact (spUCited_mem_inf_normalizer_iff (K := K) hr y).mpr ⟨hyU, hye2⟩

theorem spUCited_normal (hr : 2 ≤ r) :
    ((unipotent r K ⊓
        Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))).subgroupOf
      (spUCitedPar r K)).Normal := by
  have hQle : unipotent r K ⊓
      Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K)) ≤
        spUCitedPar r K := by

    rw [spUCitedPar]
    exact inf_le_left.trans (unipotent_le_borelSubgroup.trans
      (borelSubgroup_le_flagStabilizer (I := Set.Icc 2 r) (fun i hi => hi.2)))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQle]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact spUCited_conj_mem_inf_normalizer (K := K) hr hg hx
  · intro hx
    have hinv : g⁻¹ ∈ spUCitedPar r K := (spUCitedPar r K).inv_mem hg
    have hconj := spUCited_conj_mem_inf_normalizer (K := K) hr hinv hx
    have hsimp : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rwa [hsimp] at hconj

end CFSG.LocalAnalysis.WeakClosure81

end
