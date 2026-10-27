module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_eleven_of_exists (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D)
    (hrk : ∀ R : Subgroup G, InNM2 D (IOf D p L) B R →
      ∃ E : Subgroup G, E ≤ IOf D p L ⊓ normalizer (R : Set G) ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ 2) :
    R19_11At D V₀ V p L A t B r h := by
  have : Fact (Nat.Prime p) := ⟨(D.sig_prime p h.hyp.hp).1⟩
  intro R hR
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p (S17.calLp_subset_calC D p h.hyp.hL).1.le
  obtain ⟨E, hEI, hEel, hEcard⟩ := hrk R hR
  have hEII : E ≤ IOf D p L := (le_inf_iff.mp hEI).1
  have hEIN : E ≤ normalizer (R : Set G) := (le_inf_iff.mp hEI).2
  have hEM : E ≤ D.M := hEII.trans hIM
  have hEp : IsPGroup p E := hEel.isPGroup
  have hnc : ¬ IsCyclic E :=
    CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hEel hEcard.ge
  have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
    refine CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall D.maxLocal hEM ?_
    intro H hH hEH
    have hmem : H ∈ calMOf E := ⟨hH, hEH⟩
    rw [h61 p h.hyp.hp E hEM hEp hnc] at hmem
    simpa using hmem
  have hNE : normalizer (E : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hEU
  have hEY : E ≤ D.M ⊓ normalizer (R : Set G) := le_inf hEM hEIN
  have hY : UniqueMax D.M (D.M ⊓ normalizer (R : Set G)) := by
    have hcal : calMOf E = {D.M} := h61 p h.hyp.hp E hEM hEp hnc
    refine Set.Subset.antisymm ?_ ?_
    · intro H hH
      have hmem : H ∈ calMOf E := ⟨hH.1, hEY.trans hH.2⟩
      rw [hcal] at hmem
      exact hmem
    · intro H hH
      rw [Set.mem_singleton_iff] at hH
      subst H
      exact ⟨D.maxLocal, inf_le_left⟩
  refine ⟨?_, hY⟩
  unfold UC6.calCGS
  refine iSup_le fun C => iSup_le fun hCne => iSup_le fun hCR => iSup_le fun hCch => ?_
  have hC2 : IsPGroup 2 C := hR.2.1.to_le hCR
  have hEC : E ≤ normalizer (C : Set G) := by
    intro e he
    have heR : e ∈ normalizer (R : Set G) := hEIN he
    have heR' : e⁻¹ ∈ normalizer (R : Set G) := Subgroup.inv_mem _ heR
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : (C.subgroupOf R).Characteristic := hCch
      have hx' : x ∈ (C.subgroupOf R).map R.subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le hCR]
      have h := uc22br4_conj_mem_map_of_characteristic (D := C.subgroupOf R) heR hx'
      rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
    · intro hx
      have : (C.subgroupOf R).Characteristic := hCch
      have hx' : e * x * e⁻¹ ∈ (C.subgroupOf R).map R.subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le hCR]
      have h := uc22br4_conj_mem_map_of_characteristic (D := C.subgroupOf R) heR' hx'
      rw [Subgroup.map_subgroupOf_eq_of_le hCR] at h
      simpa [mul_assoc] using h
  have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hCne, hC2, rfl⟩
  obtain ⟨H, hHmax, hHle⟩ := UC6.exists_rankThreeIsMaxTwoLocal_ge_uc6 hloc
  have hHE : E ≤ H := hEC.trans hHle
  have hHM : H = D.M := by
    have hmem : H ∈ calMOf E := ⟨hHmax, hHE⟩
    rw [h61 p h.hyp.hp E hEM hEp hnc] at hmem
    simpa using hmem
  rwa [hHM] at hHle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
