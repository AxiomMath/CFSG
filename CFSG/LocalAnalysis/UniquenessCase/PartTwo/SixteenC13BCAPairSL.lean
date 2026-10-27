module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Matrix

section

variable {K : Type} [Field K]

private abbrev s16c13bcA_e (K : Type) [Zero K] [One K] (i : Fin 5) : Fin 5 → K :=
  Pi.single i 1

private def s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K :=
  !![1, 0, 0, 0, 0;
     0, 0, -1, 0, 0;
     0, 1, -1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

private def s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, -1;
     0, 0, 0, 1, -1]

private theorem s16c13bcA_Am_eq :
    s16c13bcA_Am = Matrix.transvection (1 : Fin 5) (2 : Fin 5) (-1 : K) *
      Matrix.transvection (2 : Fin 5) (1 : Fin 5) (1 : K) *
      Matrix.transvection (1 : Fin 5) (2 : Fin 5) (-2 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16c13bcA_Am, Matrix.mul_apply, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Fin.succ_zero_eq_one] <;> ring

private theorem s16c13bcA_Bm_eq :
    s16c13bcA_Bm = Matrix.transvection (3 : Fin 5) (4 : Fin 5) (-1 : K) *
      Matrix.transvection (4 : Fin 5) (3 : Fin 5) (1 : K) *
      Matrix.transvection (3 : Fin 5) (4 : Fin 5) (-2 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16c13bcA_Bm, Matrix.mul_apply, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Fin.succ_zero_eq_one] <;> ring

private theorem s16c13bcA_detA : (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [s16c13bcA_Am_eq, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transvection_of_ne (1 : Fin 5) (2 : Fin 5) (by decide) (-1 : K),
    Matrix.det_transvection_of_ne (2 : Fin 5) (1 : Fin 5) (by decide) (1 : K),
    Matrix.det_transvection_of_ne (1 : Fin 5) (2 : Fin 5) (by decide) (-2 : K)]
  ring

private theorem s16c13bcA_detB : (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [s16c13bcA_Bm_eq, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transvection_of_ne (3 : Fin 5) (4 : Fin 5) (by decide) (-1 : K),
    Matrix.det_transvection_of_ne (4 : Fin 5) (3 : Fin 5) (by decide) (1 : K),
    Matrix.det_transvection_of_ne (3 : Fin 5) (4 : Fin 5) (by decide) (-2 : K)]
  ring

private theorem s16c13bcA_Am3 : (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16c13bcA_Am, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one] <;> ring

private theorem s16c13bcA_Bm3 : (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16c13bcA_Bm, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one] <;> ring

private theorem s16c13bcA_ABm :
    (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) * s16c13bcA_Bm =
      s16c13bcA_Bm * s16c13bcA_Am := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16c13bcA_Am, s16c13bcA_Bm, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one] <;> ring

private theorem s16c13bcA_Am_e0 :
    (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 =
      s16c13bcA_e K 0 := by
  funext i
  fin_cases i <;>
    simp [s16c13bcA_Am, s16c13bcA_e, Matrix.mulVec_apply_eq_sum, Matrix.one_apply,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one]

private theorem s16c13bcA_Bm_e0 :
    (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 =
      s16c13bcA_e K 0 := by
  funext i
  fin_cases i <;>
    simp [s16c13bcA_Bm, s16c13bcA_e, Matrix.mulVec_apply_eq_sum, Matrix.one_apply,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one]

private theorem s16c13bcA_Am_e3 :
    (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 3 =
      s16c13bcA_e K 3 := by
  funext i
  fin_cases i <;>
    simp [s16c13bcA_Am, s16c13bcA_e, Matrix.mulVec_apply_eq_sum, Matrix.one_apply,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one]

private theorem s16c13bcA_Bm_e3 :
    (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 3 =
      s16c13bcA_e K 4 := by
  funext i
  fin_cases i <;>
    simp [s16c13bcA_Bm, s16c13bcA_e, Matrix.mulVec_apply_eq_sum, Matrix.one_apply,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one]

private theorem s16c13bcA_e_ne :
    s16c13bcA_e K 4 ≠ s16c13bcA_e K 3 := by
  intro h
  have := congrFun h 4
  simp [s16c13bcA_e] at this

private noncomputable def s16c13bcA_gA : GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K)
    (by rw [s16c13bcA_detA]; exact one_ne_zero)

private noncomputable def s16c13bcA_gB : GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K)
    (by rw [s16c13bcA_detB]; exact one_ne_zero)

private theorem s16c13bcA_gA3 : (s16c13bcA_gA : GL (Fin 5) K) ^ 3 = 1 := by
  apply Units.ext
  change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) ^ 3 = 1
  exact s16c13bcA_Am3

private theorem s16c13bcA_gB3 : (s16c13bcA_gB : GL (Fin 5) K) ^ 3 = 1 := by
  apply Units.ext
  change (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) ^ 3 = 1
  exact s16c13bcA_Bm3

private theorem s16c13bcA_gA_ne : (s16c13bcA_gA : GL (Fin 5) K) ≠ 1 := by
  intro h
  have h11 : (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) 1 1 = 1 := by
    have := congrFun (congrFun (congrArg (fun u : GL (Fin 5) K =>
      (u : Matrix (Fin 5) (Fin 5) K)) h) 1) 1
    change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) 1 1 = 1 at this
    exact this
  simp [s16c13bcA_Am] at h11

private theorem s16c13bcA_gB_ne : (s16c13bcA_gB : GL (Fin 5) K) ≠ 1 := by
  intro h
  have h34 : (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) 3 4 = 0 := by
    have := congrFun (congrFun (congrArg (fun u : GL (Fin 5) K =>
      (u : Matrix (Fin 5) (Fin 5) K)) h) 3) 4
    change (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) 3 4 = 0 at this
    exact this
  simp [s16c13bcA_Bm] at h34

private theorem s16c13bcA_orderOf_gA : orderOf (s16c13bcA_gA : GL (Fin 5) K) = 3 :=
  orderOf_eq_prime s16c13bcA_gA3 s16c13bcA_gA_ne

private theorem s16c13bcA_orderOf_gB : orderOf (s16c13bcA_gB : GL (Fin 5) K) = 3 :=
  orderOf_eq_prime s16c13bcA_gB3 s16c13bcA_gB_ne

private theorem s16c13bcA_gAB :
    (s16c13bcA_gA : GL (Fin 5) K) * s16c13bcA_gB = s16c13bcA_gB * s16c13bcA_gA := by
  apply Units.ext
  change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) * s16c13bcA_Bm =
    s16c13bcA_Bm * s16c13bcA_Am
  exact s16c13bcA_ABm

private theorem s16c13bcA_gA_e0 :
    (s16c13bcA_gA : GL (Fin 5) K) • s16c13bcA_e K 0 =
      s16c13bcA_e K 0 := by
  change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 =
    s16c13bcA_e K 0
  exact s16c13bcA_Am_e0

private theorem s16c13bcA_gB_e0 :
    (s16c13bcA_gB : GL (Fin 5) K) • s16c13bcA_e K 0 =
      s16c13bcA_e K 0 := by
  change (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 =
    s16c13bcA_e K 0
  exact s16c13bcA_Bm_e0

private theorem s16c13bcA_gA_e3 :
    (s16c13bcA_gA : GL (Fin 5) K) • s16c13bcA_e K 3 =
      s16c13bcA_e K 3 := by
  change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 3 =
    s16c13bcA_e K 3
  exact s16c13bcA_Am_e3

private theorem s16c13bcA_gB_e3 :
    (s16c13bcA_gB : GL (Fin 5) K) • s16c13bcA_e K 3 =
      s16c13bcA_e K 4 := by
  change (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 3 =
    s16c13bcA_e K 4
  exact s16c13bcA_Bm_e3

private theorem s16c13bcA_gB_notmem :
    (s16c13bcA_gB : GL (Fin 5) K) ∉ Subgroup.zpowers (s16c13bcA_gA : GL (Fin 5) K) := by
  intro hmem
  have hstab : Subgroup.zpowers (s16c13bcA_gA : GL (Fin 5) K) ≤
      MulAction.stabilizer (GL (Fin 5) K) (s16c13bcA_e K 3) :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact s16c13bcA_gA_e3)
  have hfix := hstab hmem
  rw [MulAction.mem_stabilizer_iff, s16c13bcA_gB_e3] at hfix
  exact s16c13bcA_e_ne hfix

private theorem s16c13bcA_permGL_single (σ : Equiv.Perm (Fin 5)) :
    ((permGL σ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 =
      s16c13bcA_e K (σ 0) := by
  rw [permGL_mulVec]
  funext x
  simp only [Function.comp_apply, s16c13bcA_e]
  by_cases hx : σ⁻¹ x = 0
  · rw [hx, Pi.single_eq_same]
    have hx' : x = σ 0 := by simpa using congrArg σ hx
    rw [hx', Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (i := (0 : Fin 5)) (i' := σ⁻¹ x) hx]
    have hne : x ≠ σ 0 := by
      intro h
      apply hx
      rw [h]
      exact Equiv.symm_apply_apply σ 0
    rw [Pi.single_eq_of_ne (i := σ 0) (i' := x) hne]

private theorem s16c13bcA_det_conj {g : GL (Fin 5) K}
    (hg : (g : Matrix (Fin 5) (Fin 5) K).det = 1) (C : GL (Fin 5) K) :
    ((C * g * C⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using hg
  have h2 : Matrix.GeneralLinearGroup.det (C * g * C⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, map_inv, mul_one, mul_inv_cancel]
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    using congrArg Units.val h2

private theorem s16c13bcA_transfer {g₁ g₂ : GL (Fin 5) K}
    (hd₁ : (g₁ : Matrix (Fin 5) (Fin 5) K).det = 1)
    (hd₂ : (g₂ : Matrix (Fin 5) (Fin 5) K).det = 1)
    (h₁ : orderOf g₁ = 3) (h₂ : orderOf g₂ = 3)
    (hc : g₁ * g₂ = g₂ * g₁) (hn : g₂ ∉ Subgroup.zpowers g₁)
    {w : Fin 5 → K} (hw₁ : g₁ • w = w) (hw₂ : g₂ • w = w) :
    ∃ G₁ G₂ : CFSG.Open.StatedSL 5 K, orderOf G₁ = 3 ∧ orderOf G₂ = 3 ∧
      G₁ * G₂ = G₂ * G₁ ∧ G₂ ∉ Subgroup.zpowers G₁ ∧ G₁ • w = w ∧ G₂ • w = w := by
  have hd₁' : g₁ ∈ CFSG.Open.StatedSL 5 K := Subgroup.subset_closure hd₁
  have hd₂' : g₂ ∈ CFSG.Open.StatedSL 5 K := Subgroup.subset_closure hd₂
  refine ⟨⟨g₁, hd₁'⟩, ⟨g₂, hd₂'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact h₁
  · rw [Subgroup.orderOf_mk]; exact h₂
  · apply Subtype.ext; simpa using hc
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hn
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg (fun G : CFSG.Open.StatedSL 5 K => (G : GL (Fin 5) K)) hk
    simpa [Subgroup.coe_zpow] using this
  · exact hw₁
  · exact hw₂

end

theorem s16c13bcA_pairFixed_statedSL {K : Type} [Field K] :
    s16c13bcA_PairFixed (CFSG.Open.StatedSL 5 K) (Fin 5 → K) := by
  intro v
  have hA3 : orderOf (s16c13bcA_gA (K := K)) = 3 := s16c13bcA_orderOf_gA
  have hB3 : orderOf (s16c13bcA_gB (K := K)) = 3 := s16c13bcA_orderOf_gB
  have hAB : (s16c13bcA_gA (K := K)) * s16c13bcA_gB = s16c13bcA_gB * s16c13bcA_gA :=
    s16c13bcA_gAB
  have hBnot : s16c13bcA_gB ∉ Subgroup.zpowers (s16c13bcA_gA (K := K)) :=
    s16c13bcA_gB_notmem
  by_cases hv : v = 0
  · subst hv
    refine s16c13bcA_transfer (g₁ := s16c13bcA_gA (K := K)) (g₂ := s16c13bcA_gB (K := K))
      s16c13bcA_detA s16c13bcA_detB hA3 hB3 hAB hBnot ?_ ?_
    · change (s16c13bcA_Am : Matrix (Fin 5) (Fin 5) K) *ᵥ (0 : Fin 5 → K) = 0
      exact Matrix.mulVec_zero _
    · change (s16c13bcA_Bm : Matrix (Fin 5) (Fin 5) K) *ᵥ (0 : Fin 5 → K) = 0
      exact Matrix.mulVec_zero _
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    set C : GL (Fin 5) K := colUnit i v hi * permGL (Equiv.swap 0 i) with hC
    have hperm : ((permGL (Equiv.swap 0 i) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 = s16c13bcA_e K i := by
      simpa [Equiv.swap_apply_left] using
        s16c13bcA_permGL_single (K := K) (Equiv.swap (0 : Fin 5) i)
    have hCv : C • s16c13bcA_e K 0 = v := by
      have h : ((colUnit i v hi * permGL (Equiv.swap 0 i) : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K) *ᵥ s16c13bcA_e K 0 = v := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hperm]
        exact colUnit_mulVec i v hi
      rw [hC]
      exact h
    obtain ⟨o₁, o₂, hcomm, hnot⟩ := s16c13bcA_pair_conj
      (g₁ := s16c13bcA_gA (K := K)) (g₂ := s16c13bcA_gB (K := K))
      hA3 hB3 hAB hBnot C
    refine s16c13bcA_transfer
      (g₁ := C * s16c13bcA_gA (K := K) * C⁻¹) (g₂ := C * s16c13bcA_gB (K := K) * C⁻¹)
      (s16c13bcA_det_conj (g := s16c13bcA_gA (K := K)) s16c13bcA_detA C)
      (s16c13bcA_det_conj (g := s16c13bcA_gB (K := K)) s16c13bcA_detB C)
      o₁ o₂ hcomm hnot ?_ ?_
    · rw [← hCv, mul_smul, mul_smul, inv_smul_smul, s16c13bcA_gA_e0]
    · rw [← hCv, mul_smul, mul_smul, inv_smul_smul, s16c13bcA_gB_e0]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
