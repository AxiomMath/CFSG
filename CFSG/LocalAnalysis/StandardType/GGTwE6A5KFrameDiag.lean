module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups

private theorem diagUnitOne_fix_HSL {Ω : Type} [Field Ω] (s ζ : Ωˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL ζ) = HSL ζ := by
  refine Subtype.ext ?_
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv, CFSG.LieType.Chevalley.coe_HSL]
  have hs : (s : Ω) * (s : Ω)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (ζ : Ω) * hs


private theorem frame_blockSL2_HSL_mem {τ : Tag} {Ω : Type} [Field Ω] {m : ℕ}
    {ψ : SL(m + 1, Ω) →* ModGL τ Ω} {σ' : Fin (m + 1) → Fin (m + 1) → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (c : Fin m) (t : Ωˣ) :
    ψ (blockSL2 Ω m c (HSL t)) ∈ torusGroup τ Ω := by
  have hne : c.castSucc ≠ c.succ := (Fin.castSucc_lt_succ (i := c)).ne
  have hβ := hψ.isRoot _ _ hne
  obtain ⟨a, ha⟩ := hψ.transv _ _ hne
  obtain ⟨b, hb⟩ := hψ.transv _ _ hne.symm
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 hβ (ψ.comp (blockSL2 Ω m c)) a b
    (fun u => by rw [MonoidHom.comp_apply, blockSL2_uSL_eq, ha])
    (fun u => by rw [MonoidHom.comp_apply, blockSL2_vSL_eq, hb, hψ.neg c.castSucc c.succ])
  have h := DFunLike.congr_fun hs (HSL t)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, diagUnitOne_fix_HSL] at h
  rw [h]
  exact rootSL2_HSL_mem_torusGroup hβ t

private theorem frame_diag_aux {τ : Tag} {Ω : Type} [Field Ω] {m : ℕ}
    {ψ : SL(m + 1, Ω) →* ModGL τ Ω} {σ' : Fin (m + 1) → Fin (m + 1) → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (k : ℕ) : k ≤ m → ∀ δ ∈ KSGen.diagSL (m + 1) Ω,
      (∀ j : Fin (m + 1), k < (j : ℕ) → (δ : Matrix (Fin (m + 1)) (Fin (m + 1)) Ω) j j = 1) →
      ψ δ ∈ torusGroup τ Ω := by
  induction k with
  | zero =>
    intro _ δ hδ h1
    obtain ⟨x, hx, rfl⟩ := KSGen.exists_units_of_mem_diagSL hδ
    have hx1 : ∀ i : Fin m, x i.succ = 1 := fun i => by
      simpa [KSGen.coe_diagSLOf] using h1 i.succ (by simp)
    have h0 : x 0 = 1 := by
      rwa [Fin.prod_univ_succ, Finset.prod_eq_one fun i _ => hx1 i, mul_one] at hx
    have hx' : x = 1 := funext fun j => Fin.cases h0 hx1 j
    subst hx'
    rw [show KSGen.diagSLOf (1 : Fin (m + 1) → Ωˣ) hx = 1 from
      Subtype.ext (by simp [KSGen.coe_diagSLOf]), map_one]
    exact one_mem _
  | succ k ih =>
    intro hk δ hδ h1
    obtain ⟨x, hx, rfl⟩ := KSGen.exists_units_of_mem_diagSL hδ
    obtain ⟨c, hc⟩ : ∃ c : Fin m, (c : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
    obtain ⟨j₁, hj₁⟩ : ∃ j : Fin (m + 1), (j : ℕ) = k + 1 := ⟨⟨k + 1, by omega⟩, rfl⟩
    have hb : blockSL2 Ω m c (HSL (x j₁)) ∈ KSGen.diagSL (m + 1) Ω :=
      KSGen.mem_diagSL.2 fun i j hij => by rw [coe_blockSL2_HSL, Matrix.diagonal_apply_ne _ hij]
    have key := ih (by omega) _ (mul_mem (KSGen.diagSLOf_mem x hx) hb) fun j hj => by
      have hj' := h1 j
      simp only [Matrix.SpecialLinearGroup.coe_mul, KSGen.coe_diagSLOf, coe_blockSL2_HSL,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at hj' ⊢
      split_ifs with h2 h3
      · exact absurd h2 (by omega)
      · rw [show j = j₁ from Fin.ext (by omega), Units.mul_inv]
      · rw [mul_one]
        exact hj' (by omega)
    have := mul_mem key (inv_mem (frame_blockSL2_HSL_mem hψ c (x j₁)))
    rwa [← map_inv ψ, ← map_mul ψ, mul_inv_cancel_right] at this

theorem frame_diagSL_mem_torusGroup {τ : Tag} {Ω : Type} [Field Ω] {ν : ℕ}
    {ψ : SL(ν, Ω) →* ModGL τ Ω} {σ' : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ')
    {δ : SL(ν, Ω)} (hδ : δ ∈ KSGen.diagSL ν Ω) : ψ δ ∈ torusGroup τ Ω := by
  cases ν with
  | zero =>
    rw [Subsingleton.elim δ 1, map_one]
    exact one_mem _
  | succ m => exact frame_diag_aux hψ m le_rfl δ hδ fun j hj => absurd j.2 (by omega)

end CFSG.StandardType.SCFourCover
