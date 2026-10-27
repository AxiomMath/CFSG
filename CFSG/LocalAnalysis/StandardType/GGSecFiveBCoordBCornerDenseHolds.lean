module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerAbsorb
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseMark
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseUniFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal

section Inputs


theorem ggSecFiveBCoordBCornerDenseInput_holds : GGSecFiveBCoordBCornerDenseInput := by
  intro hMp hX hTCJ hRig hTPn hA8 hraw hiso hFC hLJ hU62 G _ _ p B Bs x L D J
    𝒦 hR hTier n e hPres hn4 eta i0 hAjoin hAL hLab hne hBrow hRows hNbr hG0
    r π κ ζ hπ0 hframe g hg hgG0 hτ K hDense
  classical
  obtain ⟨lab, hΛ, hHas, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hLab
  have hp3 : p = 3 := hP.1.2.2.2.2
  have hn : 5 ≤ n := hP.1.2.1
  subst p
  have hncard : r + 2 = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr π
  have hr : 3 ≤ r := by omega
  obtain ⟨hxL', hsplit⟩ := hR.1.1.cornerSplit_of_planeFrame hAL hframe
  obtain ⟨R, z, c, hD, hc, hJ, hRow⟩ := hRows
  obtain ⟨a, b, hab, s, hs, hW, hu, hCode, hRank⟩ :=
    hR.cornerRowRest_rowThree_of_denseNbr hn4 hAL hxL' hsplit R z hD hRow hDense
  have hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, n - 1, 1⟩ : LargeEvenLabel)) 3 Bs K := by
    refine largeEvenMarking_mono ?_
      (hR.cornerRowThree_denseNbr_marking hLJ hRig hn hAjoin hAL R hu hCode hc hJ hDense)
    rintro ⟨t, m, f⟩ A _ I F θ ⟨⟨ht, hm, hf, -⟩, hN, hI⟩
    change t = .twA at ht
    change m = n - 1 at hm
    change f = 1 at hf
    subst t m f
    exact ⟨rfl, hN, hI⟩
  have hlt : B < Bs := lt_of_le_of_ne hR.1.1.2.1.1 hne
  obtain ⟨d, hd, F, hFld, hFin, hChar, σ, χ, hF, hKF⟩ :=
    hDense.exists_unitary_frame_of_marking hR.1.1 hlt hn eta hmark (Equiv.refl _)
  have h01 : π (0 : Fin (r + 2)) ≠ π 1 := by
    intro he
    have hv := congrArg Fin.val (π.injective he)
    simp only [Fin.val_zero, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < r + 2)] at hv
    omega
  exact hKF.le_sup_map_conj_of_original_swap hF Nat.prime_three (by omega)
    eta d hd h01 hg hτ (fun S hS h0 => hR.ggBlockComm_le_of_corner hframe hr S hS h0)


end Inputs

end CFSG.StandardType

end
