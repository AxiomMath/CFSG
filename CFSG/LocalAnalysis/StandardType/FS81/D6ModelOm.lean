module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelRel
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.SeitzReduction.OmegaPilot

theorem le_Om12_of_pair {W X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hp : LinearBlockStandardPair (ZMod 2) W X Y)
    (hX : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q12)
    (hY : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q12) : X ≤ Om12 ∧ Y ≤ Om12 := by
  have hWsup : W = X ⊔ Y := CFSG.StandardType.linearBlockStandardPair_eq_sup hp
  obtain ⟨θ, c, hrange, -, -⟩ := hp
  have hperf : ⁅W, W⁆ = W := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := ZMod 2) (n := 3)
      le_rfl
  have hWO : W ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := hWsup ▸ sup_le hX hY
  have hWΩ : W ≤ Om12 := by
    calc W = ⁅W, W⁆ := hperf.symm
      _ ≤ Om12 := Subgroup.commutator_mono hWO hWO
  exact ⟨le_trans le_sup_left (hWsup ▸ hWΩ), le_trans le_sup_right (hWsup ▸ hWΩ)⟩

theorem rootL_le_O12 (B P : Finset (Fin 6)) :
    rootL B P ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
  have hC : isometryClosure (ZMod 2) 6 ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q12).comap lin :=
    (CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus (n := 6) (K := ZMod 2))).le
  have hS : siegelBlockGL (ZMod 2) B ≤ isometryClosure (ZMod 2) 6 :=
    (siegelBlockGL_le_omegaLeviSL B).trans
      (omegaLeviSL_le_omegaLeviGL.trans omegaLeviGL_le_isometryClosure)
  have hf : flipGL (ZMod 2) P ∈ isometryClosure (ZMod 2) 6 :=
    Subgroup.subset_closure (flipGL_isometry P)
  rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  exact hC (Subgroup.mul_mem _ (Subgroup.mul_mem _ hf (hS hx)) (Subgroup.inv_mem _ hf))

theorem node_le_Om12 (j : Fin 6) : node j ≤ Om12 := by
  have hO : ∀ k, node k ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := fun k => rootL_le_O12 _ _
  obtain ⟨W₀, h₀⟩ := node_pair (i := 0) (j := 1) (by decide)
  obtain ⟨W₂, h₂⟩ := node_pair (i := 2) (j := 3) (by decide)
  obtain ⟨W₄, h₄⟩ := node_pair (i := 3) (j := 4) (by decide)
  obtain ⟨W₅, h₅⟩ := node_pair (i := 3) (j := 5) (by decide)
  fin_cases j
  · exact (le_Om12_of_pair h₀ (hO 0) (hO 1)).1
  · exact (le_Om12_of_pair h₀ (hO 0) (hO 1)).2
  · exact (le_Om12_of_pair h₂ (hO 2) (hO 3)).1
  · exact (le_Om12_of_pair h₂ (hO 2) (hO 3)).2
  · exact (le_Om12_of_pair h₄ (hO 3) (hO 4)).2
  · exact (le_Om12_of_pair h₅ (hO 3) (hO 5)).2

theorem flip0_le_Om12 : flip0 ≤ Om12 := by
  obtain ⟨W, h⟩ := flip0_pair_node1
  exact (le_Om12_of_pair h (rootL_le_O12 _ _) (rootL_le_O12 _ _)).1

theorem flip2_le_Om12 : flip2 ≤ Om12 := by
  obtain ⟨W, h⟩ := flip2_pair_node1
  exact (le_Om12_of_pair h (rootL_le_O12 _ _) (rootL_le_O12 _ _)).2

end CFSG.StandardType.FrameRoute.FS81.D6M
