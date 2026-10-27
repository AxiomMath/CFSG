module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Quasithin.H13.U4ParPoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Borel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer hypBorel_le_flagStabilizer
  flagStabilizer_singleton mem_flagStabilizer mem_isoStabilizer overgroupCuts
  unitary_Borel_overgroups normalizer_hypUnitriangular uWeylRep uWeylRep_mem_flagStabilizer_iff)

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

theorem su4_exists_sylow_hypUnitriangular :
    ∃ U : Sylow 2 ↥(hypSU h 2 0), (U : Subgroup ↥(hypSU h 2 0)) = hypUnitriangular h 2 0 :=
  (unitary_order_and_Sylow h (by norm_num) (by norm_num)).2.1

theorem su4_hypUnitriangular_le_parP : hypUnitriangular h 2 0 ≤ parP h := fun _ hg =>
  (Subgroup.mem_inf.mp
    ((su4_parP_inf_flagStabilizer_eq_hypBorel h).ge (hypUnitriangular_le_hypBorel h hg))).1

theorem su4_hypUnitriangular_le_flagStabilizer_two :
    hypUnitriangular h 2 0 ≤ flagStabilizer h 2 0 {2} :=
  (hypUnitriangular_le_hypBorel h).trans
    (hypBorel_le_flagStabilizer (Set.singleton_subset_iff.mpr ⟨by norm_num, le_rfl⟩))

theorem su4_isParabolicTwo_flagStabilizer_two :
    IsParabolicTwo ↥(hypSU h 2 0) (flagStabilizer h 2 0 {2}) := by
  obtain ⟨U, hU⟩ := su4_exists_sylow_hypUnitriangular h
  refine ⟨U, ?_⟩
  show Subgroup.normalizer ((U : Subgroup ↥(hypSU h 2 0)) : Set ↥(hypSU h 2 0)) ≤
    flagStabilizer h 2 0 {2}
  rw [hU, normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
  exact hypBorel_le_flagStabilizer (Set.singleton_subset_iff.mpr ⟨by norm_num, by norm_num⟩)

theorem su4_not_flagStabilizer_two_le_parP : ¬ flagStabilizer h 2 0 {2} ≤ parP h := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  intro hle
  have hI1 : ({1} : Set ℕ) ⊆ Set.Icc 1 2 :=
    Set.singleton_subset_iff.mpr ⟨by norm_num, by norm_num⟩
  have hI2 : ({2} : Set ℕ) ⊆ Set.Icc 1 2 :=
    Set.singleton_subset_iff.mpr ⟨by norm_num, by norm_num⟩
  have hmem2 : uWeylRep 0 h (0 : Fin 2) c hc ∈ flagStabilizer h 2 0 ({2} : Set ℕ) :=
    (uWeylRep_mem_flagStabilizer_iff h (by norm_num) hc hc0 hI2 (0 : Fin 2)).mpr (by norm_num)
  have hmemP : uWeylRep 0 h (0 : Fin 2) c hc ∈ parP h := hle hmem2
  have hmem1 : uWeylRep 0 h (0 : Fin 2) c hc ∈ flagStabilizer h 2 0 ({1} : Set ℕ) := by
    rw [flagStabilizer_singleton]
    exact hmemP
  exact (uWeylRep_mem_flagStabilizer_iff h (by norm_num) hc hc0 hI1 (0 : Fin 2)).mp hmem1
    (by norm_num)

theorem su4_flagStabilizer_two_le_of_parabolic {P : Subgroup ↥(hypSU h 2 0)}
    (hP : IsParabolicTwo ↥(hypSU h 2 0) P) (hU : hypUnitriangular h 2 0 ≤ P)
    (hnot : ¬ P ≤ parP h) : flagStabilizer h 2 0 {2} ≤ P := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨U, hUeq⟩ := su4_exists_sylow_hypUnitriangular h
  have hUP : (U : Subgroup ↥(hypSU h 2 0)) ≤ P := by
    rw [hUeq]
    exact hU
  have hBP : hypBorel h 2 0 ≤ P := by
    rw [← normalizer_hypUnitriangular h (by norm_num) (by norm_num), ← hUeq]
    exact hP.normalizer_le U hUP
  obtain ⟨hI, hPI, -, -⟩ :=
    unitary_Borel_overgroups h (by norm_num) (by norm_num) hc hc0 P hBP
  have h1I : (1 : ℕ) ∉ overgroupCuts 0 h c hc P := by
    intro h1
    apply hnot
    rw [hPI]
    intro g hg
    exact mem_isoStabilizer.mpr ((mem_flagStabilizer.mp hg) 1 h1)
  rw [hPI]
  intro g hg
  rw [mem_flagStabilizer] at hg
  rw [mem_flagStabilizer]
  intro i hi
  have hine : i ≠ 1 := fun e => h1I (e ▸ hi)
  obtain ⟨hi1, hi2⟩ := hI hi
  have hieq : i = 2 := by omega
  rw [hieq]
  exact hg 2 rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
