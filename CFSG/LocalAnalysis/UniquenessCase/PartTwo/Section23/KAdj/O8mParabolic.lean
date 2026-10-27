module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

theorem omegaMinusTailQZero_eq_t3Pℓ0 (K : Type) [Field K] (b c : K) :
    omegaMinusTailQZero K b c = t3Pℓ0 K b c := by
  ext x
  rw [mem_orthParab, Fin.forall_fin_two,
    mem_stabilizer_iff_map (Q := quadTail 3 (minusTailForm K b c))]
  constructor
  · rintro ⟨-, h1⟩
    simpa using h1
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero, tailFlag_zero, Submodule.map_bot]
    · simpa using h

theorem t3P0_le_omegaMinusTailQAlpha {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : t3P0 K b c ≤ omegaMinusTailQAlpha K b c := by
  have hani := t3q_anisotropic hirr
  have ha0 := t3a0_ne_zero K
  intro x hx
  have hx' : (x : T3V K ≃ₗ[K] T3V K) ∈
      tailRankOneParabolic (minusTailForm K b c) (t3a0 K) (0 : Fin 3) :=
    Subgroup.mem_subgroupOf.1 hx
  refine mem_orthParab.2 fun i => ?_
  have key : tailRankOneParabolic (minusTailForm K b c) (t3a0 K) (0 : Fin 3) ≤
      MulAction.stabilizer (T3V K ≃ₗ[K] T3V K)
        (tailFlag K (Fin 2 → K) 3 ((![0, 2, 3] : Fin 3 → ℕ) i)) := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro g (hg | hg)
    · fin_cases i
      · change Submodule.map _ (tailFlag K (Fin 2 → K) 3 0) =
          tailFlag K (Fin 2 → K) 3 0
        rw [tailFlag_zero, Submodule.map_bot]
      · exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
          ((mem_tailBorel.1 hg).2 2 (by norm_num) (by norm_num))
      · exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
          ((mem_tailBorel.1 hg).2 3 (by norm_num) (by norm_num))
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      fin_cases i
      · change Submodule.map _ (tailFlag K (Fin 2 → K) 3 0) =
          tailFlag K (Fin 2 → K) 3 0
        rw [tailFlag_zero, Submodule.map_bot]
      · exact MulAction.mem_stabilizer_iff.2
          ((tailWeylElt_smul_tailFlag hani ha0 (1 : Fin 3) 0).2 (by decide))
      · exact MulAction.mem_stabilizer_iff.2
          ((tailWeylElt_smul_tailFlag hani ha0 (2 : Fin 3) 0).2 (by decide))
  exact Submodule.mem_stabilizer_submodule_iff_map_eq.1 (key hx')

theorem omegaMinusTailQAlpha_le_t3P0 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : omegaMinusTailQAlpha K b c ≤ t3P0 K b c := by
  have hani := t3q_anisotropic hirr
  have ha0 := t3a0_ne_zero K
  have hfix : ∀ i : Fin 3, ∀ g ∈ (omegaMinusTailQAlpha K b c).map (T3G K b c).subtype,
      g • tailFlag K (Fin 2 → K) 3 ((![0, 2, 3] : Fin 3 → ℕ) i) =
        tailFlag K (Fin 2 → K) 3 ((![0, 2, 3] : Fin 3 → ℕ) i) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact mem_orthParab.1 hx i
  have hBM : tailBorel 3 (minusTailForm K b c) ≤
      (omegaMinusTailQAlpha K b c).map (T3G K b c).subtype := by
    intro g hg
    refine ⟨⟨g, tailBorel_le hg⟩, mem_orthParab.2 fun i => ?_, rfl⟩
    fin_cases i
    · change Submodule.map _ (tailFlag K (Fin 2 → K) 3 0) = tailFlag K (Fin 2 → K) 3 0
      rw [tailFlag_zero, Submodule.map_bot]
    · exact (mem_tailBorel.1 hg).2 2 (by norm_num) (by norm_num)
    · exact (mem_tailBorel.1 hg).2 3 (by norm_num) (by norm_num)
  have hcl := tail_eq_closure_of_borel_le hani ha0 (Subgroup.map_subtype_le _) hBM
  intro x hx
  have hxM : (x : T3V K ≃ₗ[K] T3V K) ∈
      (omegaMinusTailQAlpha K b c).map (T3G K b c).subtype :=
    ⟨x, hx, rfl⟩
  rw [hcl] at hxM
  refine Subgroup.mem_subgroupOf.2 (Subgroup.closure_mono ?_ hxM)
  rintro g (hg | ⟨i, hi, rfl⟩)
  · exact Or.inl hg
  · right
    rw [Set.mem_singleton_iff]
    have hi' : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈
        (omegaMinusTailQAlpha K b c).map (T3G K b c).subtype := hi
    have h2 := hfix 1 _ hi'
    have h3 := hfix 2 _ hi'
    fin_cases i
    · rfl
    · exact absurd h2 ((tailWeylElt_smul_tailFlag hani ha0 (1 : Fin 3) 1).not.mpr (by simp))
    · exact absurd h3 ((tailWeylElt_smul_tailFlag hani ha0 (2 : Fin 3) 2).not.mpr (by simp))

theorem omegaMinusTailQAlpha_eq_t3P0 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : omegaMinusTailQAlpha K b c = t3P0 K b c :=
  le_antisymm (omegaMinusTailQAlpha_le_t3P0 hirr) (t3P0_le_omegaMinusTailQAlpha hirr)

theorem t3U_le_omegaMinusTailQZero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : t3U K b c ≤ omegaMinusTailQZero K b c := by
  rw [omegaMinusTailQZero_eq_t3Pℓ0]
  intro x hx
  exact tailBorel_le_stabilizer_t3F1 hirr
    (tailUnipotent_le_tailBorel (t3q_anisotropic hirr) (Subgroup.mem_subgroupOf.mp hx))

theorem isParabolicTwo_omegaMinusTailQAlpha {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo (OmegaMinusE K b c) (omegaMinusTailQAlpha K b c) := by
  rw [omegaMinusTailQAlpha_eq_t3P0 hirr]
  exact t3P0_isParabolic hirr

theorem t3U_le_omegaMinusTailQAlpha {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : t3U K b c ≤ omegaMinusTailQAlpha K b c := by
  rw [omegaMinusTailQAlpha_eq_t3P0 hirr]
  exact t3U_le_t3P0 hirr

theorem not_omegaMinusTailQAlpha_le_QZero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ omegaMinusTailQAlpha K b c ≤ omegaMinusTailQZero K b c := by
  rw [omegaMinusTailQAlpha_eq_t3P0 hirr, omegaMinusTailQZero_eq_t3Pℓ0]
  exact t3P0_not_le_t3Pℓ0 hirr

theorem omegaMinusTailQAlpha_le_of_parabolic {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {P : Subgroup (OmegaMinusE K b c)}
    (hP : IsParabolicTwo (OmegaMinusE K b c) P) (hU : t3U K b c ≤ P)
    (hnot : ¬ P ≤ omegaMinusTailQZero K b c) : omegaMinusTailQAlpha K b c ≤ P := by
  have hB : t3B K b c ≤ P := by
    have h := hP.normalizer_le (t3Sylow hirr) (by rw [t3Sylow_coe]; exact hU)
    change Subgroup.normalizer
      (((t3Sylow hirr : Subgroup ↥(T3G K b c)) : Set ↥(T3G K b c))) ≤ P at h
    rwa [t3Sylow_coe, ← t3B_eq_normalizer hirr] at h
  rw [omegaMinusTailQZero_eq_t3Pℓ0] at hnot
  rw [omegaMinusTailQAlpha_eq_t3P0 hirr]
  exact t3P0_le_of_borel_le_of_not_le_point hirr hB hnot

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
