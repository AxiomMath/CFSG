module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Minus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.UniquenessCase.UC22.OmegaMinus6Tail
open scoped Pointwise

variable {K : Type} [Field K] {b c : K}

private lemma stabilizer_tailFlag_one_eq_orthParab_I03 {K : Type} [Field K] {A : Type}
    [AddCommGroup A] [Module K A] {r : ℕ} (qA : QuadraticForm K A) :
    MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) (tailFlag K A r 1) =
      orthParab r qA ![0, 1] := by
  ext x
  rw [mem_stabilizer_iff_map (Q := quadTail r qA), mem_orthParab, Fin.forall_fin_two]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero, tailFlag_zero, Submodule.map_bot]
    · simpa using h
  · rintro ⟨-, h1⟩
    simpa using h1

private lemma mem_orthParab_two_I03 {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A]
    (qA : QuadraticForm K A) {x : ↥(orthElementaryGroup (quadTail 2 qA))} :
    x ∈ orthParab 2 qA ![0, 2] ↔
      (tailFlag K A 2 2).map
        (((x : ((Fin 2 ⊕ Fin 2 → K) × A) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × A)) :
          ((Fin 2 ⊕ Fin 2 → K) × A) →ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × A))) =
        tailFlag K A 2 2 := by
  rw [mem_orthParab, Fin.forall_fin_two]
  constructor
  · rintro ⟨-, h2⟩
    simpa using h2
  · intro h2
    exact ⟨by simp only [Matrix.cons_val_zero, tailFlag_zero, Submodule.map_bot],
      by simpa using h2⟩

theorem om6m_orthParab_one_eq_T2Pℓ0 :
    orthParab 2 (minusTailForm K b c) ![0, 1] = T2Pℓ0 K b c := by
  rw [T2Pℓ0, T2F1]
  exact (stabilizer_tailFlag_one_eq_orthParab_I03 (minusTailForm K b c)).symm

private lemma om6m_T2B_le_orthParab_two_I03 :
    T2B K b c ≤ orthParab 2 (minusTailForm K b c) ![0, 2] := by
  intro x hx
  rw [mem_orthParab_two_I03]
  exact (mem_tailBorel.1 (Subgroup.mem_subgroupOf.mp hx)).2 2 (by norm_num) (by norm_num)

private lemma om6m_orthParab_two_ne_top_I03 [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    orthParab 2 (minusTailForm K b c) ![0, 2] ≠ ⊤ := by
  intro htop
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  have hn1G : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1 ∈ T2G K b c :=
    tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 1
  have hn1 : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1, hn1G⟩ :
      ↥(T2G K b c)) ∈ orthParab 2 (minusTailForm K b c) ![0, 2] := by
    rw [htop]
    exact Subgroup.mem_top _
  have hfixmap := (mem_orthParab_two_I03 (minusTailForm K b c)).1 hn1
  have hn1stab : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1, hn1G⟩ :
      ↥(T2G K b c)) ∈ MulAction.stabilizer (T2G K b c) (T2F2 K) :=
    (mem_stabilizer_iff_map (Q := quadTail 2 (minusTailForm K b c))).2
      (by simpa [T2F2] using hfixmap)
  have hfix : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1 • T2F2 K = T2F2 K :=
    MulAction.mem_stabilizer_iff.1 hn1stab
  exact ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) hani ha0 1 1).1 hfix) rfl

private lemma om6m_not_orthParab_two_le_T2Pℓ0_I03 [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ orthParab 2 (minusTailForm K b c) ![0, 2] ≤ T2Pℓ0 K b c := by
  intro hle
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  have hn0G : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈ T2G K b c :=
    tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0
  have hn0P : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0, hn0G⟩ :
      ↥(T2G K b c)) ∈ orthParab 2 (minusTailForm K b c) ![0, 2] := by
    rw [mem_orthParab_two_I03]
    have hfix0 : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 • T2F2 K = T2F2 K :=
      (tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
        (a₀ := t2a0 K) hani ha0 1 0).2 (by decide)
    exact (mem_stabilizer_iff_map (Q := quadTail 2 (minusTailForm K b c))).1
      (MulAction.mem_stabilizer_iff.2 hfix0)
  have hn0Pℓ := hle hn0P
  rw [T2Pℓ0] at hn0Pℓ
  have hfix := MulAction.mem_stabilizer_iff.1 hn0Pℓ
  have hfix' : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 • T2F1 K = T2F1 K := hfix
  exact ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) hani ha0 0 0).1 hfix') rfl

theorem om6m_orthParab_two_eq_T2P0 [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    orthParab 2 (minusTailForm K b c) ![0, 2] = T2P0 K b c :=
  T2P0_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr
    (om6m_T2B_le_orthParab_two_I03 (K := K) (b := b) (c := c))
    (om6m_orthParab_two_ne_top_I03 (K := K) (b := b) (c := c) hirr)
    (om6m_not_orthParab_two_le_T2Pℓ0_I03 (K := K) (b := b) (c := c) hirr)

theorem om6m_exists_sylow_tailUnipotent [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ U : Sylow 2 ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))),
      (U : Subgroup ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) =
        (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
          (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
  ⟨t2Sylow K b c hirr, t2Sylow_coe K b c hirr⟩

theorem om6m_isParabolicTwo_orthParab_two [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))
      (orthParab 2 (minusTailForm K b c) ![0, 2]) := by
  rw [om6m_orthParab_two_eq_T2P0 hirr]
  exact T2P0_isParabolic K b c hirr

theorem om6m_not_orthParab_two_le_one [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ orthParab 2 (minusTailForm K b c) ![0, 2] ≤ orthParab 2 (minusTailForm K b c) ![0, 1] := by
  rw [om6m_orthParab_two_eq_T2P0 hirr, om6m_orthParab_one_eq_T2Pℓ0]
  exact T2P0_not_le_T2Pℓ0 K b c hirr

theorem om6m_orthParab_two_le_of_parabolic [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hP : IsParabolicTwo ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) P)
    (hU : (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) ≤ P)
    (hnot : ¬ P ≤ orthParab 2 (minusTailForm K b c) ![0, 1]) :
    orthParab 2 (minusTailForm K b c) ![0, 2] ≤ P := by
  have hB : T2B K b c ≤ P := by
    rw [T2B_eq_normalizer K b c hirr, ← t2Sylow_coe K b c hirr]
    exact hP.normalizer_le (t2Sylow K b c hirr) hU
  have hnot' : ¬ P ≤ T2Pℓ0 K b c := by
    simpa [om6m_orthParab_one_eq_T2Pℓ0] using hnot
  have hP0 : T2P0 K b c ≤ P :=
    T2P0_le_of_borel_le_of_not_le_point K b c hirr hB hnot'
  rw [om6m_orthParab_two_eq_T2P0 hirr]
  exact hP0

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
