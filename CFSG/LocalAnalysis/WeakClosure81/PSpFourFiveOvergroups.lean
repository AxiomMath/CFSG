module

public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups
public import CFSG.LocalAnalysis.WeakClosure81.PSpFourOrthogonalModel
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.Blueprint
open CFSG

theorem exists_overgroups_of_psp4_five
    (L₀ : Type) [Group L₀] [Finite L₀]
    (hLie : LieModel L₀ .PSp 2 5 1)
    (A S : Subgroup (MulAut L₀)) (hAS : AlmostSimpleData L₀ A S) :
    ∃ X1 X2 : Subgroup (MulAut L₀),
      S ≤ X1 ∧ S ≤ X2 ∧
      X1 ≤ A ∧ X2 ≤ A ∧
      ¬ innAutOf L₀ ≤ X1 ∧ ¬ innAutOf L₀ ≤ X2 ∧
      (X1 ⊓ innAutOf L₀) ⊔ (X2 ⊓ innAutOf L₀) = innAutOf L₀ := by
  obtain ⟨ρ, hρinj, hρrange, hρinn, htrans⟩ :=
    exists_orthogonal_model_of_lieModel_psp_prime (p := 5) (by norm_num) (by norm_num)
      (hK := by rw [Nat.card_zmod])
      (Q := CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Q)
      (hQ := by
        exact CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Generic.polar_nondegenerate
          CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.F)
      (hdim := by simp) L₀ hLie
  obtain ⟨hDG, hGSO, hSylow, hDsup⟩ := htrans A S hAS
  let G : Subgroup ↥(CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.O) := A.map ρ
  let P : Subgroup G := (S.map ρ).subgroupOf G
  have hP2 : IsPGroup 2 ↥P :=
    hSylow.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSylow.le).symm
  have hPindex : ¬ 2 ∣ P.index := by
    change ¬ 2 ∣ (S.map ρ).relIndex G
    exact hSylow.not_dvd_relIndex
  let T : Sylow 2 G := hP2.toSylow hPindex
  have hTcoe : (T : Subgroup G) = P := IsPGroup.toSylow_coe hP2 hPindex
  have hTmap : (T : Subgroup G).map G.subtype = S.map ρ := by
    rw [hTcoe]
    dsimp only [P]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSylow.le]
  have hodd : Odd (Nat.card CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.F) := by
    rw [Nat.card_zmod]; norm_num
  have hdim : Module.finrank
      CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.F
      (Fin 5 → CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.F) = 5 := by simp
  obtain ⟨X1, X2, hT_le_X1, hT_le_X2, hX1_le_G, hX2_le_G,
    hnotD_X1, hnotD_X2, hX1Djoin⟩ :=
    exists_overgroups_of_frame (F := CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.stdFrame)
      hodd
      (CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Generic.polar_nondegenerate
        CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.F)
      hdim G hDG hGSO T C0 M0 generation_inf not_D0_le_C0 not_D0_le_M0
      wreathO_le_C0 wreathO_le_M0
  have hSmap_le_X1 : S.map ρ ≤ X1 := by
    rw [← hTmap]
    exact hT_le_X1
  have hSmap_le_X2 : S.map ρ ≤ X2 := by
    rw [← hTmap]
    exact hT_le_X2
  let Y1 : Subgroup (MulAut L₀) := Subgroup.comap ρ X1
  let Y2 : Subgroup (MulAut L₀) := Subgroup.comap ρ X2
  have hS_le_Y1 : S ≤ Y1 := by
    dsimp only [Y1]
    exact Subgroup.map_le_iff_le_comap.mp hSmap_le_X1
  have hS_le_Y2 : S ≤ Y2 := by
    dsimp only [Y2]
    exact Subgroup.map_le_iff_le_comap.mp hSmap_le_X2
  have hY1_le_A : Y1 ≤ A := by
    dsimp only [Y1]
    calc Subgroup.comap ρ X1 ≤ Subgroup.comap ρ (A.map ρ) := Subgroup.comap_mono hX1_le_G
      _ = A := Subgroup.comap_map_eq_self_of_injective hρinj A
  have hY2_le_A : Y2 ≤ A := by
    dsimp only [Y2]
    calc Subgroup.comap ρ X2 ≤ Subgroup.comap ρ (A.map ρ) := Subgroup.comap_mono hX2_le_G
      _ = A := Subgroup.comap_map_eq_self_of_injective hρinj A
  have hnotInn_Y1 : ¬ innAutOf L₀ ≤ Y1 := by
    intro h
    have hmap : (innAutOf L₀).map ρ ≤ X1 :=
      Subgroup.map_le_iff_le_comap.mpr h
    rw [hρinn] at hmap
    exact hnotD_X1 hmap
  have hnotInn_Y2 : ¬ innAutOf L₀ ≤ Y2 := by
    intro h
    have hmap : (innAutOf L₀).map ρ ≤ X2 :=
      Subgroup.map_le_iff_le_comap.mpr h
    rw [hρinn] at hmap
    exact hnotD_X2 hmap
  have hX1_range : X1 ≤ ρ.range := by
    exact le_trans hX1_le_G (Subgroup.map_le_range ρ A)
  have hX2_range : X2 ≤ ρ.range := by
    exact le_trans hX2_le_G (Subgroup.map_le_range ρ A)
  have hjoin_comap :
      (Subgroup.comap ρ X1 ⊓ innAutOf L₀) ⊔
        (Subgroup.comap ρ X2 ⊓ innAutOf L₀) = innAutOf L₀ := by
    have h := congrArg (Subgroup.comap ρ) hX1Djoin
    rw [← Subgroup.comap_sup_eq_of_le_range ρ
      (le_trans inf_le_left hX1_range) (le_trans inf_le_left hX2_range)] at h
    change Subgroup.comap ρ
        (X1 ⊓ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Q)) ⊔
      Subgroup.comap ρ
        (X2 ⊓ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Q)) =
      Subgroup.comap ρ
        (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration.Q)) at h
    rw [← hρinn] at h
    rw [Subgroup.comap_inf X1 ((innAutOf L₀).map ρ) ρ,
      Subgroup.comap_inf X2 ((innAutOf L₀).map ρ) ρ] at h
    rw [Subgroup.comap_map_eq_self_of_injective hρinj (innAutOf L₀)] at h
    exact h
  exact ⟨Y1, Y2, hS_le_Y1, hS_le_Y2, hY1_le_A, hY2_le_A,
    hnotInn_Y1, hnotInn_Y2, by simpa only [Y1, Y2] using hjoin_comap⟩

end CFSG.LocalAnalysis.WeakClosure81
