module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

theorem Hyp88.exists_gammaSet_not_le_normalizer {V H T : Subgroup G} {i : ℕ}
    (h : Hyp88 V H T i) :
    ∃ A ∈ E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H ∧
      ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G) := by
  by_contra hcon
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.calH h.sylow
  have hTM : T ≤ Subgroup.normalizer (V : Set G) := h.sylow.le.trans inf_le_right
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH h.calH h.sylow
  have key : ∀ A ∈ E3.gammaSet V i T, ∀ x ∈ H,
      conjSubgroup A x ≤ Subgroup.normalizer (V : Set G) := by
    intro A hA x hx
    by_contra hnot
    refine hcon ⟨A, hA, ?_, x, hx, hnot⟩
    intro hA0
    have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hx
    have h1 : conjSubgroup A x ≤ conjSubgroup (pCoreOf 2 H) x :=
      E3.conjSubgroup_mono_left x hA0
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hxN] at h1
    exact hnot (h1.trans (hOT.trans hTM))
  have hK0 : ∀ A ∈ E3.gammaSet V i T, A ≤ kerMV V H := by
    intro A hA
    have hAH : A ≤ H := hA.1.trans hTH.le
    have hNcH : CFSG.Quasithin.conjClosure A H ≤ H :=
      CFSG.Quasithin.conjClosure_le fun h' hh' z hz =>
        H.mul_mem (H.mul_mem hh' (hAH hz)) (H.inv_mem hh')
    have hNcn : ∀ h' ∈ H, ∀ n ∈ CFSG.Quasithin.conjClosure A H,
        h' * n * h'⁻¹ ∈ CFSG.Quasithin.conjClosure A H := by
      intro h' hh' n hn
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.le_normalizer_conjClosure A H hh') n).1 hn
    have hNcM : CFSG.Quasithin.conjClosure A H ≤ Subgroup.normalizer (V : Set G) := by
      refine CFSG.Quasithin.conjClosure_le fun h' hh' z hz => ?_
      refine key A hA h'⁻¹ (H.inv_mem hh') ?_
      rw [mem_conjSubgroup_iff]
      have hz' : h'⁻¹ * (h' * z * h'⁻¹) * (h'⁻¹)⁻¹ = z := by group
      rw [hz']
      exact hz
    have hANc : A ≤ CFSG.Quasithin.conjClosure A H := by
      intro a ha
      simpa using CFSG.Quasithin.mem_conjClosure H.one_mem ha
    exact hANc.trans (le_kerMV_of_normal hNcH hNcn hNcM)
  have hKH : kerMV V H ≤ H := kerMV_le_self V H
  have hKnormal : ((kerMV V H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact conj_mem_kerMV (V := V) (H := H) hg hn
    · intro hn
      have h' := conj_mem_kerMV (V := V) (H := H) (H.inv_mem hg) hn
      have he : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
      rwa [he] at h'
  have hP : IsSylowIn 2 (T ⊓ kerMV V H) (kerMV V H) := hTH.inf_normal hKH hKnormal
  have hWP : E3.wClos V i T ≤ T ⊓ kerMV V H :=
    le_inf (E3.wClos_le i T) (E3.wClos_le_of_forall fun A hA => hK0 A hA)
  have hNP : Subgroup.normalizer (T ⊓ kerMV V H : Set G) ≤
      Subgroup.normalizer (E3.wClos V i T : Set G) :=
    E3.e3_15_normalizer hTH (inf_le_left.trans hTH.le) (hTH.isPGroup.to_le inf_le_left) hWP
  refine h.notLe ?_
  intro x hx
  obtain ⟨k, hk, n, hn, hxkn⟩ := frattini_argument hKH hKnormal hP hx
  have hkM : k ∈ Subgroup.normalizer (V : Set G) := kerMV_le_normalizer V H hk
  have hnH : n ∈ H := (Subgroup.mem_inf.mp hn).1
  have hnP : n ∈ Subgroup.normalizer (T ⊓ kerMV V H : Set G) := (Subgroup.mem_inf.mp hn).2
  have hnW : n ∈ Subgroup.normalizer (E3.wClos V i T : Set G) := hNP hnP
  have hnM : n ∈ Subgroup.normalizer (V : Set G) :=
    h.normW (Subgroup.mem_inf.mpr ⟨hnH, hnW⟩)
  rw [hxkn]
  exact Subgroup.mul_mem _ hkM hnM

end CFSG.LocalAnalysis.WeakClosure81

end
