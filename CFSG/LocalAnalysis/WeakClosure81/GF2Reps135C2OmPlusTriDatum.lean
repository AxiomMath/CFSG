module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriRoots
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.Timmesfeld CFSG.ClassicalInvolution.G2D4Models.Twin

section Datum

variable {F : Type} [Field F] {ρ : spinGroup (Spin.quadPlus 4 F) ≃* spinGroup (Spin.quadPlus 4 F)}

theorem map_posUnipotent_le_of_pinned (hρ : IsTrialityPinned ρ) :
    (posUnipotent (Spin.plusDatum 4 F (by norm_num))).map ρ.toMonoidHom ≤
      posUnipotent (Spin.plusDatum 4 F (by norm_num)) := by
  unfold posUnipotent
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  obtain ⟨h1, h2⟩ := map_plusRootGroup_of_pinned hρ hγ.1
  have hht : ht (γ ∘ ⇑triEquiv.symm) = ht γ := Equiv.sum_comp triEquiv.symm γ
  exact (h2.le).trans (rootGroup_le_posUnipotent (D := Spin.plusDatum 4 F (by norm_num)) h1
    (lt_of_lt_of_eq hγ.2 hht.symm))

variable [Finite F] [CharP F 2]

theorem omPlusCurtisDatum_triality (hρ : IsTrialityPinned ρ) :
    (∀ u ∈ (omPlusCurtisDatum 4 F (by norm_num)).U,
        ρ u ∈ (omPlusCurtisDatum 4 F (by norm_num)).U) ∧
      (∀ h ∈ (omPlusCurtisDatum 4 F (by norm_num)).H,
        ρ h ∈ (omPlusCurtisDatum 4 F (by norm_num)).H) ∧
      (∀ (s : Fin 4) (x : spinGroup (Spin.quadPlus 4 F)),
        x ∈ (omPlusCurtisDatum 4 F (by norm_num)).X s ↔
          ρ x ∈ (omPlusCurtisDatum 4 F (by norm_num)).X (triPerm s)) ∧
      ∀ s : Fin 4, ρ ((omPlusCurtisDatum 4 F (by norm_num)).n s) =
        (omPlusCurtisDatum 4 F (by norm_num)).n (triPerm s) := by
  refine ⟨fun u hu => ?_, fun h hh => ?_, fun s x => ?_, fun s => ?_⟩
  · rw [omPlusCurtisDatum_U] at hu ⊢
    exact map_posUnipotent_le_of_pinned hρ ⟨u, hu, rfl⟩
  · rw [omPlusCurtisDatum_H] at hh ⊢
    have hle : (⨆ k, (Spin.torusD F (by norm_num) k).range).map ρ.toMonoidHom ≤
        ⨆ k, (Spin.torusD F (by norm_num) k).range := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact Subgroup.mem_iSup_of_mem (triPerm k) ⟨a, (map_torusD_of_pinned hρ k a).symm⟩
    exact hle ⟨h, hh, rfl⟩
  · rw [omPlusCurtisDatum_X, omPlusCurtisDatum_X]
    have hm := map_plusRootGroup_single_of_pinned hρ s
    constructor
    · intro hx
      rw [← hm]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hm] at hx
      obtain ⟨g, hg, hgx⟩ := hx
      exact (ρ.injective hgx) ▸ hg
  · rw [omPlusCurtisDatum_n, omPlusCurtisDatum_n]
    exact map_weylD_of_pinned hρ s

end Datum

end CFSG.LocalAnalysis.WeakClosure81
