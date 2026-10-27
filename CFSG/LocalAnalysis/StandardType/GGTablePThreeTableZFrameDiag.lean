module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section FrameDiag

open CFSG.ClassicalInvolution.WeakCT CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint

private theorem tzFD_diagUnitOne_fix_HSL {Ω : Type} [Field Ω] (s ζ : Ωˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL ζ) = HSL ζ := by
  refine Subtype.ext ?_
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv, CFSG.LieType.Chevalley.coe_HSL]
  have hs : (s : Ω) * (s : Ω)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (ζ : Ω) * hs

private theorem tzFD_frame_blockSL2_HSL_eq
    {L : Type} [Field L]
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (c : Fin 2) (u : Lˣ) :
    ψ (blockSL2 L 2 c (HSL u)) =
      rootDiagUnit Tag.E6 (fun j => u ^ corootPair (σ' c.castSucc c.succ) (Pi.single j 1)) := by
  have hne : c.castSucc ≠ c.succ := (Fin.castSucc_lt_succ (i := c)).ne
  have hβ := hψ.isRoot c.castSucc c.succ hne
  obtain ⟨a, ha⟩ := hψ.transv c.castSucc c.succ hne
  obtain ⟨b, hb⟩ := hψ.transv c.succ c.castSucc hne.symm
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_comp_conjSL_eq_rootSL2
    hβ (ψ.comp (blockSL2 L 2 c)) a b
    (fun t => by rw [MonoidHom.comp_apply, blockSL2_uSL_eq, ha])
    (fun t => by rw [MonoidHom.comp_apply, blockSL2_vSL_eq, hb, hψ.neg c.castSucc c.succ])
  calc ψ (blockSL2 L 2 c (HSL u))
      = (ψ.comp (blockSL2 L 2 c)) (HSL u) := rfl
    _ = (ψ.comp (blockSL2 L 2 c))
          (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL u)) := by
        rw [tzFD_diagUnitOne_fix_HSL]
    _ = rootSL2 Tag.E6 L (σ' c.castSucc c.succ) (HSL u) := DFunLike.congr_fun hs (HSL u)
    _ = rootDiagUnit Tag.E6 (fun j => u ^ corootPair (σ' c.castSucc c.succ) (Pi.single j 1)) :=
        rootSL2_HSL_eq hβ u

private theorem tzFD_corootPair_single_eq_iform
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (j : Fin Tag.E6.rank) :
    corootPair β (Pi.single j 1) = iform (Pi.single j 1) β := by
  have h2 : iform β β = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hβ
  have h := corootPair_mul hβ (Pi.single j 1)
  rw [h2] at h
  rw [iform_comm]
  omega

end FrameDiag

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint in
theorem tableZ_frame_diag
    {L : Type} [Field L] [IsAlgClosed L]
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    (c : SL(3, L)) (t : Fin 3 → Lˣ)
    (hc : (c : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun k => (t k : L)) :
    ψ c = rootDiagUnit Tag.E6 fun j =>
      t 0 ^ (iform (Pi.single j 1) (σ' 0 1) + iform (Pi.single j 1) (σ' 1 2)) *
        t 1 ^ iform (Pi.single j 1) (σ' 1 2) := by
  have hdet : (t 0 : L) * t 1 * t 2 = 1 := by
    have := c.2
    rw [hc, Matrix.det_diagonal, Fin.prod_univ_three] at this
    exact this
  have hdec : c =
      CFSG.ClassicalInvolution.WeakCT.blockSL2 L 2 0 (HSL (t 0)) *
        CFSG.ClassicalInvolution.WeakCT.blockSL2 L 2 1 (HSL (t 0 * t 1)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, CFSG.HardMathSupport.Timmesfeld.CrossChar.coe_blockSL2_HSL,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.coe_blockSL2_HSL, hc,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j
    · simp
    · simp
    · simp
      have h0 : (t 0 : L) ≠ 0 := (t 0).ne_zero
      have h1 : (t 1 : L) ≠ 0 := (t 1).ne_zero
      field_simp
      linear_combination hdet
  have hb0 := tzFD_frame_blockSL2_HSL_eq hψ (0 : Fin 2) (t 0)
  have hb1 := tzFD_frame_blockSL2_HSL_eq hψ (1 : Fin 2) (t 0 * t 1)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hb0
  simp only [Fin.castSucc_one, Fin.succ_one_eq_two] at hb1
  rw [hdec, map_mul, hb0, hb1, ← rootDiagUnit_mul]
  refine congrArg (rootDiagUnit Tag.E6) ?_
  funext j
  simp only [Pi.mul_apply]
  rw [tzFD_corootPair_single_eq_iform (hψ.isRoot 0 1 (by decide)) j,
    tzFD_corootPair_single_eq_iform (hψ.isRoot 1 2 (by decide)) j,
    mul_zpow, ← mul_assoc, ← zpow_add]

end CFSG.StandardType.TablePThreeKG

end
