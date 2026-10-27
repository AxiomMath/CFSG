module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoSpChart
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.StandardType.FieldTwoPOmega

open Matrix
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.StandardType.RankOneXfer (sl2UpperUniSub mem_sl2UpperUniSub_iff
  closure_sl2Upper_sl2Lower_eq_top)
open CFSG.StandardType.ClassicalPosition (siegelGroup)
open CFSG.StandardType.FieldTwoPSp (ShortPairsG shortChartGL shortChartGL_injective
  coe_shortChartGL_sl2Upper coe_shortChartGL_sl2Lower exists_models_of_chart)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply elementaryGroup
  eichler_mem_elementaryGroup)
open CFSG.LieType.Universal (UniversalRootDatum)
open CFSG.LieType.Universal.Spin (spinAction spinMatrix coe_spinMatrix)

section Gram

variable {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] (Q : QuadraticForm F (σ → F))

abbrev polarMat : Matrix σ σ F :=
  LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)

theorem polar_eq_dotProduct_polarMat (x y : σ → F) :
    QuadraticMap.polar Q x y = x ⬝ᵥ polarMat Q *ᵥ y := by
  rw [polarMat, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix',
    QuadraticMap.polarBilin_apply_apply]

theorem polarMat_transpose : (polarMat Q)ᵀ = polarMat Q := by
  ext i j
  rw [Matrix.transpose_apply, polarMat, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm]

theorem polarMat_self [CharP F 2] (x : σ → F) : x ⬝ᵥ polarMat Q *ᵥ x = 0 := by
  rw [← polar_eq_dotProduct_polarMat, QuadraticMap.polar_self, two_nsmul,
    CharTwo.add_self_eq_zero]

variable {Q}

theorem shortPairsG_polarMat {a₁ a₂ b₁ b₂ : σ → F} (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) :
    ShortPairsG (polarMat Q) a₁ a₂ b₁ b₂ := by
  simp only [ShortPairsG, ← polar_eq_dotProduct_polarMat]
  exact ⟨h₁, h₂, h₀⟩

theorem toMatrix'_eichler [CharP F 2] {u w : σ → F} (hu : Q u = 0) (hw : Q w = 0)
    (huw : QuadraticMap.polar Q u w = 0) (t : F) :
    LinearMap.toMatrix' ((eichler Q u (t • w) : (σ → F) ≃ₗ[F] σ → F) : (σ → F) →ₗ[F] σ → F) =
      1 + t • (vecMulVec u (polarMat Q *ᵥ w) + vecMulVec w (polarMat Q *ᵥ u)) := by
  have hp : QuadraticMap.polar Q u (t • w) = 0 := by
    rw [QuadraticMap.polar_smul_right, huw, smul_zero]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, LinearEquiv.coe_coe, eichler_apply hu hp, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, QuadraticMap.polar_smul_right,
    QuadraticMap.map_smul, hw, smul_zero, zero_mul, add_zero, polar_eq_dotProduct_polarMat,
    polar_eq_dotProduct_polarMat, dotProduct_comm x, dotProduct_comm x, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq, smul_eq_mul]
  module

end Gram

section SpinChart

variable {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] [CharP F 2]
  {Q : QuadraticForm F (σ → F)} {a₁ a₂ b₁ b₂ : σ → F}

omit [CharP F 2] in
theorem spinMatrix_injective (hinjA : Function.Injective (spinAction Q)) :
    Function.Injective (spinMatrix Q) := by
  intro x y h
  apply hinjA
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  rw [← coe_spinMatrix, ← coe_spinMatrix, h]

private theorem coe_spinMatrix_of_eichler {u w : σ → F} (hu : Q u = 0) (hw : Q w = 0)
    (huw : QuadraticMap.polar Q u w = 0) (t : F) {s : spinGroup Q}
    (hs : spinAction Q s = eichler Q u (t • w)) :
    (spinMatrix Q s : Matrix σ σ F) =
      1 + t • (vecMulVec u (polarMat Q *ᵥ w) + vecMulVec w (polarMat Q *ᵥ u)) := by
  rw [coe_spinMatrix, hs, toMatrix'_eichler hu hw huw]

theorem exists_spinChart (hinjA : Function.Injective (spinAction Q))
    (hE : elementaryGroup Q ≤ (spinAction Q).range)
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup Q, Function.Injective c ∧
      (∀ t, spinAction Q (c (sl2Upper t)) = eichler Q a₁ (t • a₂)) ∧
      ∀ t, spinAction Q (c (sl2Lower t)) = eichler Q b₁ (t • b₂) := by
  have hP := shortPairsG_polarMat h₁ h₂ h₀
  let c₀ := shortChartGL (polarMat_transpose Q) (polarMat_self Q) hP
  have hinj := spinMatrix_injective hinjA
  have hU : ∀ t, ∃ s : spinGroup Q, spinMatrix Q s = c₀ (sl2Upper t) ∧
      spinAction Q s = eichler Q a₁ (t • a₂) := by
    intro t
    obtain ⟨s, hs⟩ := hE (eichler_mem_elementaryGroup Q a₁ (t • a₂))
    refine ⟨s, Units.ext ?_, hs⟩
    rw [coe_spinMatrix_of_eichler hQ.1 hQ.2.1 h₀.1 t hs, coe_shortChartGL_sl2Upper]
  have hL : ∀ t, ∃ s : spinGroup Q, spinMatrix Q s = c₀ (sl2Lower t) ∧
      spinAction Q s = eichler Q b₁ (t • b₂) := by
    intro t
    obtain ⟨s, hs⟩ := hE (eichler_mem_elementaryGroup Q b₁ (t • b₂))
    refine ⟨s, Units.ext ?_, hs⟩
    rw [coe_spinMatrix_of_eichler hQ.2.2.1 hQ.2.2.2 h₀.2.1 t hs, coe_shortChartGL_sl2Lower]
  have hrange : ∀ A, c₀ A ∈ (spinMatrix Q).range := by
    intro A
    have hle : Subgroup.closure (Set.range (sl2Upper : F → _) ∪ Set.range (sl2Lower : F → _)) ≤
        (spinMatrix Q).range.comap c₀ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · obtain ⟨s, hs, -⟩ := hU t
        exact ⟨s, hs⟩
      · obtain ⟨s, hs, -⟩ := hL t
        exact ⟨s, hs⟩
    exact hle (by rw [closure_sl2Upper_sl2Lower_eq_top]; trivial)
  let e := MonoidHom.ofInjective hinj
  let c : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup Q :=
    e.symm.toMonoidHom.comp (c₀.codRestrict (spinMatrix Q).range hrange)
  have hc : ∀ A, spinMatrix Q (c A) = c₀ A := fun A =>
    congrArg Subtype.val (e.apply_symm_apply ⟨c₀ A, hrange A⟩)
  refine ⟨c, fun A B h => shortChartGL_injective (polarMat_transpose Q) (polarMat_self Q) hP
    (by rw [← hc, ← hc, h]), fun t => ?_, fun t => ?_⟩
  · obtain ⟨s, hs, hsE⟩ := hU t
    rw [hinj ((hc _).trans hs.symm)]
    exact hsE
  · obtain ⟨s, hs, hsE⟩ := hL t
    rw [hinj ((hc _).trans hs.symm)]
    exact hsE

theorem exists_spinChart_siegel (hinjA : Function.Injective (spinAction Q))
    (hE : elementaryGroup Q ≤ (spinAction Q).range)
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup Q, Function.Injective c ∧
      ((sl2UpperUniSub F).map c).map (spinAction Q) = siegelGroup Q a₁ a₂ ∧
      ∀ t, spinAction Q (c (sl2Lower t)) ∈ siegelGroup Q b₁ b₂ := by
  obtain ⟨c, hc, hU, hL⟩ := exists_spinChart hinjA hE hQ h₁ h₂ h₀
  refine ⟨c, hc, le_antisymm ?_ ?_, fun t => Subgroup.subset_closure ⟨t, hL t⟩⟩
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hA
    exact Subgroup.subset_closure ⟨t, hU t⟩
  · rw [siegelGroup, Subgroup.closure_le]
    rintro g ⟨t, rfl⟩
    exact ⟨c (sl2Upper t), ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, rfl⟩, hU t⟩

end SpinChart

section Models

variable {σ : Type} [Fintype σ] [DecidableEq σ] {Q : QuadraticForm (GaloisField 2 1) (σ → GaloisField 2 1)}
  {a₁ a₂ b₁ b₂ : σ → GaloisField 2 1}

theorem exists_models_of_siegel {K' : Type*} [Group K'] {D : UniversalRootDatum (spinGroup Q)}
    {D' : UniversalRootDatum K'} (hinjA : Function.Injective (spinAction Q))
    (hE : elementaryGroup Q ≤ (spinAction Q).range) (ι : K' →* spinGroup Q)
    (hι : Function.Injective ι) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) {β₀ : Fin D'.rank → ℤ}
    (hβ₀ : β₀ ∈ D'.roots)
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0)
    (hX : ((D'.rootGroup β₀).map ι).map (spinAction Q) = siegelGroup Q a₁ a₂)
    (hX' : ((D'.rootGroup (-β₀)).map ι).map (spinAction Q) = siegelGroup Q b₁ b₂)
    (u : spinGroup Q)
    (hu : ((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map (spinAction Q) =
      siegelGroup Q a₁ a₂) :
    ∃ (model : SelectedRoot.SelectedSL2Model D (GaloisField 2 1) β)
      (model' : SelectedRoot.SelectedSL2Model D' (GaloisField 2 1) β₀),
      ∀ A, MulAut.conj u (model.phi A) = ι (model'.phi A) := by
  obtain ⟨c, hc, hcS, hcS'⟩ := exists_spinChart_siegel hinjA hE hQ h₁ h₂ h₀
  have hcU : (sl2UpperUniSub (GaloisField 2 1)).map c = (D'.rootGroup β₀).map ι :=
    Subgroup.map_injective hinjA (hcS.trans hX.symm)
  have hcL : ∀ t, c (sl2Lower t) ∈ ι.range := by
    intro t
    have hmem := hcS' t
    rw [← hX'] at hmem
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨z, hinjA hyc⟩
  exact exists_models_of_chart ι hι hβ hβ₀ c hc hcU hcL u
    (Subgroup.map_injective hinjA (hu.trans hcS.symm))

end Models

end CFSG.StandardType.FieldTwoPOmega

end
