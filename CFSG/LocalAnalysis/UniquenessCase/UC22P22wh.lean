module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p22wh_isDirectSumMod_reindex {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {m m' : ℕ}
    (σ : Fin m ≃ Fin m') {U C : Submodule (ZMod 2) V} {Ui : Fin m' → Submodule (ZMod 2) V}
    (h : IsDirectSumMod U C Ui) : IsDirectSumMod U C (fun i => Ui (σ i)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · rw [← h1]
    congr 1
    exact Equiv.iSup_comp (g := Ui) σ
  · have hre : (⨆ j ∈ {j | j ≠ i}, Ui (σ j)) = ⨆ k ∈ {k | k ≠ σ i}, Ui k := by
      refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun k hk => ?_)
      · exact le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ σ i}) => Ui k) (σ j)
          (fun h => hj (σ.injective h)) le_rfl
      · have hk' : σ.symm k ≠ i := fun h => hk (by rw [← h, Equiv.apply_symm_apply])
        refine le_iSup₂_of_le (f := fun j (_ : j ∈ {j | j ≠ i}) => Ui (σ j)) (σ.symm k) hk' ?_
        rw [Equiv.apply_symm_apply]
    simp only [hre]
    exact h2 (σ i)

end CFSG.LocalAnalysis.UniquenessCase.UC22
