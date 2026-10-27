module

public import CFSG.Timmesfeld.ARS.CaseHFeitHigman

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Orbit

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem exists_conj_of_mem_lambdaSet_of_omega {A B B' : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ omegaSet R A) (hB' : B' ∈ omegaSet R A) (hBB' : B' ∈ lambdaSet R B) :
    ∃ m ∈ M R A, conjSub B m = B' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1
  obtain ⟨C, ⟨hCR, hCle, hCψ⟩, -⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso hBR hA hB.2.symm hBB'
  have hCΩ : C ∉ omegaSet R A := notMem_omegaSet_of_mem_psiSet h hA hCψ
  have hCB : C ≠ B := fun e => hCΩ (e ▸ hB)
  have hCB' : C ≠ B' := fun e => hCΩ (e ▸ hB')
  obtain ⟨hCl, hline⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hBR hBB' hBR le_sup_left hCR hCle (Ne.symm hCB)
  have hBC : B ∈ lambdaSet R C := mem_lambdaSet_comm hBR hCl
  obtain ⟨hDA, hDC⟩ := commutator_mem_lambdaSet h hA hCR hCψ.2
  have hDR : ⁅A, C⁆ ∈ R := hDA.1.1
  have hDB : ⁅A, C⁆ ∉ lambdaSet R B := notMem_lambdaSet_of_opposite h hA hB.2 hDA
  have hnc : ¬ Commuting ⁅A, C⁆ B := by
    intro hc
    have hne : ⁅A, C⁆ ≠ B := fun e => notMem_omegaSet_of_mem_lambdaSet h hA hDA (e ▸ hB)
    exact hDB (mem_lambdaSet_of_commuting hH hBR hDR hne hc.symm)
  obtain ⟨hsDB, -⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hCR hDC hBC hnc
  have hpts : ∀ d ∈ ⁅A, C⁆, conjSub B d ∈ pointsOn R (B ⊔ B') \ {C} := by
    intro d hd
    have hdC : conjSub C d = C :=
      conjSub_of_forall_commute fun c hc => (hDC.1.2.2 c hc d hd).symm
    refine ⟨⟨hR.conjSub_mem hBR d, ?_⟩, fun e => hCB ?_⟩
    · rw [← hline, sup_comm, ← conjSub_sup_eq_of_mem_M h hCR hBC (QD.le_M hDC hd)]
      exact Subgroup.map_mono le_sup_right
    · rw [← hdC] at e
      exact (RankOne.map_conj_inj.1 (Set.mem_singleton_iff.1 e)).symm
  have hinj : Function.Injective fun d : ↥⁅A, C⁆ => conjSub B (d : G) := by
    intro d d' e
    by_contra hne
    have e' : conjSub B ((d' : G)⁻¹ * d) = B := by
      change conjSub B d = conjSub B d' at e
      rw [conjSub_mul, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h1 : (d' : G)⁻¹ * d ≠ 1 := fun h1 => hne (Subtype.ext (inv_mul_eq_one.mp h1)).symm
    exact Sec3.conjSub_ne_of_special hR hiso hDR hBR hsDB
      ((⁅A, C⁆).mul_mem ((⁅A, C⁆).inv_mem d'.2) d.2) h1 e'
  have hrange : Set.range (fun d : ↥⁅A, C⁆ => conjSub B (d : G)) = pointsOn R (B ⊔ B') \ {C} := by
    refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 fun d => hpts d d.2) ?_
      (Set.toFinite _)
    have hCm : C ∈ pointsOn R (B ⊔ B') := ⟨hCR, hCle⟩
    rw [Set.ncard_sdiff_singleton_of_mem hCm, ncard_pointsOn h hBR hBB', Nat.add_sub_cancel,
      ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hR.card_eq hDR hBR]
  have hB'm : B' ∈ pointsOn R (B ⊔ B') \ {C} :=
    ⟨⟨hB'.1, le_sup_right⟩, fun e => hCB' (Set.mem_singleton_iff.1 e).symm⟩
  rw [← hrange] at hB'm
  obtain ⟨d, hd⟩ := hB'm
  exact ⟨d, QD.le_M hDA d.2, hd⟩

end Orbit

end CaseH

end CFSG.Timmesfeld.ARS
