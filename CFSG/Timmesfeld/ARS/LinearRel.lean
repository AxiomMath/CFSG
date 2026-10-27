module

public import CFSG.Timmesfeld.ARS.LinearFrame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Linear

namespace IsFrame

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
  {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {n : ℕ} {P : Fin n → Set (Subgroup G)}
  {Q : Fin n → Subgroup G} (hfr : IsFrame R Δ P Q)
include hR hiso hnd hΩ hΔ hfr

omit [Finite G] hR hiso hnd hΩ hΔ in
theorem le_stabSet_iff_of_mem {j : Fin n} {X : Subgroup G} (hX : X ∈ dualPoint R Δ (Q j))
    (k : Fin n) : X ≤ stabSet (P k) ↔ k ≠ j := by
  rw [le_stabSet_iff_of_mem_dualPoint hX (hfr.isPoint k), hfr.le_stabSet_iff]

theorem le_stabSet_dualPoint_iff_of_mem {i : Fin n} {X : Subgroup G} (hX : X ∈ P i)
    (l : Fin n) : X ≤ stabSet (dualPoint R Δ (Q l)) ↔ i ≠ l := by
  rw [le_stabSet_dualPoint_iff hR hiso hnd hΩ hΔ (hfr.mem l) (hfr.isPoint i) hX (hfr.mem l),
    hfr.le_stabSet_iff]

theorem opposite {i j : Fin n} {X Y : Subgroup G} (hXP : X ∈ P i)
    (hXD : X ∈ dualPoint R Δ (Q j)) (hYP : Y ∈ P j) (hYD : Y ∈ dualPoint R Δ (Q i)) :
    Opposite X Y :=
  opposite_of_not_le_stabSet hR hiso hnd hΩ hΔ (hfr.isPoint i) (hfr.isPoint j) hXP hYP
    (fun h => (hfr.le_stabSet_iff_of_mem hXD j).1 h rfl)
    (fun h => (hfr.le_stabSet_iff_of_mem hYD i).1 h rfl)

theorem commuting {i j k l : Fin n} {X Y : Subgroup G} (hXP : X ∈ P i)
    (hXD : X ∈ dualPoint R Δ (Q j)) (hYP : Y ∈ P k) (hYD : Y ∈ dualPoint R Δ (Q l))
    (hil : i ≠ l) (hkj : k ≠ j) : Commuting X Y := by
  by_cases hik : i = k
  · subst hik
    exact Sec5.commuting_of_mem hR hiso hnd ((hfr.isPoint i).isWeakTI hR hΔ) hXP hYP
  · exact commuting_of_le_stabSet hR hiso hnd hΩ hΔ (hfr.isPoint i) (hfr.isPoint k)
      (hfr.ne hik) hXP hYP ((hfr.le_stabSet_iff_of_mem hXD k).2 hkj)
      ((hfr.le_stabSet_iff_of_mem hYD i).2 hil)

theorem special {i j k : Fin n} {X Y Z : Subgroup G} (hXP : X ∈ P i)
    (hXD : X ∈ dualPoint R Δ (Q j)) (hYP : Y ∈ P j) (hYD : Y ∈ dualPoint R Δ (Q k))
    (hZP : Z ∈ P i) (hZD : Z ∈ dualPoint R Δ (Q k)) (hik : i ≠ k) :
    Special R X Y ∧ ⁅X, Y⁆ = Z := by
  have hC₀ : Q k ∈ R := hfr.mem k
  have hΔ' : IsTI R (dualPoint R Δ (Q k)) := isTI_dualPoint hR hiso hnd hΩ hΔ hC₀
  have hYR : Y ∈ R := hYD.1
  have hXR : X ∈ R := hXD.1
  have hXj : ¬ X ≤ stabSet (P j) := fun h => (hfr.le_stabSet_iff_of_mem hXD j).1 h rfl
  have hnc : ¬ Commuting X Y := fun h =>
    hXj (Sec5.le_stabSet_of_commuting hR ((hfr.isPoint j).isWeakTI hR hΔ) hXR hYP h)
  obtain ⟨-, hmem1⟩ := special_of_le_stabSet hR hiso hnd hΩ hΔ (hfr.isPoint i) hYR hXP
    ((hfr.le_stabSet_iff_of_mem hYD i).2 hik) fun h => hnc h.symm
  have hDk : IsPoint (dualPoint R Δ (Q k)) (dualPoint R Δ (Q k)) := isPoint_self _
  obtain ⟨hs, hmem2⟩ := special_of_le_stabSet hR hiso hnd hΩ hΔ' hDk hXR hYD
    ((hfr.le_stabSet_dualPoint_iff_of_mem hR hiso hnd hΩ hΔ hXP k).2 hik) hnc
  refine ⟨hs, ?_⟩
  rw [Subgroup.commutator_comm] at hmem1
  exact eq_of_mem_dualPoint hR hiso hnd hΩ hΔ (hfr.isPoint i) hmem1 hZP hmem2 hZD

end IsFrame

end Linear

end CFSG.Timmesfeld.ARS
