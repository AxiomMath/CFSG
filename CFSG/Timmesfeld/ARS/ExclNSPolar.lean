module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.Sec13Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace ExclNS

theorem notMem_lambdaSet_of_mem_leviSet (h : Hyp G R) {A A₀ Y : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hY : Y ∈ leviSet R A A₀) : Y ∉ lambdaSet R A := by
  intro hYA
  apply h.root.ne_bot Y hY.1.1
  rw [eq_bot_iff, ← M_inf_levi_eq_bot h hA hA₀]
  exact le_inf (QD.le_M hYA) (le_gen hY)

variable {A A₀ : Subgroup G}

theorem exists_mem_lambdaStar_polar (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    ∃ C ∈ lambdaStar R A A₀, C ≠ B ∧ Commuting B C ∧ C ∉ lambdaSet R B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hBR : B ∈ R := hB.1.1.1
  have hAB : A ∈ lambdaSet R B := mem_lambdaSet_comm hA hB.1
  have hBA : B ≠ A := hB.1.1.2.1
  obtain ⟨B₁, hB₁R, hBB₁⟩ := hiso B hBR
  obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hBR hB₁R hBB₁ hAB
  have hPB : P ≠ B := by
    rintro rfl
    exact Special.not_opposite hR hB₁R hPψ.2 hBB₁.symm
  obtain ⟨U, hU, u, hu, hPu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hBR hAB hPR hPle hPB hA
    le_sup_right (Ne.symm hBA)
  have huB : conjSub B u = B := conjSub_of_forall_commute fun b hb => (hU.1.2.2 b hb u hu).symm
  set B₀ := conjSub B₁ u with hB₀def
  have hB₀ : B₀ ∈ omegaSet R B := ⟨hR.conjSub_mem hB₁R u, huB ▸ Opposite.conj hBB₁ u⟩
  have hAψ : A ∈ psiSet R B₀ := ⟨hA, hPu ▸ Sec3.special_conjSub hR hPψ.2 u⟩
  have hS' : Sec13 R B B₀ := hS.of_mem_omegaSet hBR hB₀
  obtain ⟨Y, hY, hYA⟩ := deltaSet_nonempty hS'.hyp hBR hS'.sec8.2 hS'.opp
    (show A ∈ lambdaStar R B B₀ from ⟨hAB, hAψ⟩)
  have hYR : Y ∈ R := hY.1.1
  have hYB : Y ∉ lambdaSet R B := notMem_lambdaSet_of_mem_leviSet hS'.hyp hBR hB₀ hY
  have hYA' : Y ∈ lambdaSet R A := hYA
  obtain ⟨C, ⟨hCR, hCle, hCψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hYA'
  have hCA : C ≠ A := by
    rintro rfl
    exact Special.not_opposite hR hA₀.1 hCψ.2 hA₀.2.symm
  have hCΛ : C ∈ lambdaSet R A :=
    (mem_lambdaSet_of_le_sup hR hiso hA hYA' hA le_sup_left hCR hCle (Ne.symm hCA)).1
  have hCB : Commuting B C :=
    ((Commuting.sup_right hB.1.1.2.2.symm hY.1.2.2).mono le_rfl hCle)
  refine ⟨C, ⟨hCΛ, hCψ⟩, ?_, hCB, ?_⟩
  · rintro rfl
    have hline := (mem_lambdaSet_of_le_sup hR hiso hA hYA' hA le_sup_left hCR hCle hBA.symm).2
    have hYle : Y ≤ C ⊔ A := by
      rw [sup_comm, hline]
      exact le_sup_right
    exact hYB (mem_lambdaSet_of_le_sup hR hiso hCR (mem_lambdaSet_comm hA hCΛ) hCR le_sup_left
      hYR hYle hY.1.2.1.symm).1
  · intro hCBΛ
    set S : Set (Subgroup G) := {A, B, C} with hSdef
    have hSR : S ⊆ R := by
      rintro _ (rfl | rfl | rfl) <;> assumption
    have hcol : ∀ X ∈ S, ∀ Z ∈ S, X ≠ Z → Z ∈ lambdaSet R X := by
      have l1 := hB.1
      have l2 := hCΛ
      have l3 := hAB
      have l4 := mem_lambdaSet_comm hA hCΛ
      have l5 := hCBΛ
      have l6 := mem_lambdaSet_comm hBR hCBΛ
      intro X hX Z hZ hXZ
      simp only [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hZ
      rcases hX with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl <;>
        first | exact absurd rfl hXZ | assumption
    have hAT : A ≤ gen S := le_gen (Set.mem_insert A _)
    have hCT : C ≤ gen S := le_gen (by simp [hSdef])
    have hBT : B ≤ gen S := le_gen (by simp [hSdef])
    have hline := (mem_lambdaSet_of_le_sup hR hiso hA hYA' hA le_sup_left hCR hCle
      (Ne.symm hCA)).2
    have hYT : Y ≤ gen S := by
      calc Y ≤ A ⊔ Y := le_sup_right
        _ = A ⊔ C := hline.symm
        _ ≤ gen S := sup_le hAT hCT
    exact hYB (Singular.mem_lambdaSet hS.hyp hSR hcol ⟨hBR, hBT⟩ ⟨hYR, hYT⟩
      hY.1.2.1.symm)

end ExclNS

end CFSG.Timmesfeld.ARS
