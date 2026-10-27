module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactMatrix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.Open.QuasithinDefs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin
open CFSG.SeitzReduction.SymplecticPilot (suppGL)

theorem leviB_eq_suppGL (m : ℕ) :
    leviB m = suppGL (ZMod 2) {i : BlkIdx 1 m | i ≠ Sum.inl 0 ∧ i ≠ Sum.inr (Sum.inr 0)} := by
  let e : Fin m → BlkIdx 1 m := fun j => Sum.inr (Sum.inl j)
  have he : Function.Injective e := by
    intro a b h
    simpa [e] using h
  have hrange : Set.range e = {i : BlkIdx 1 m | i ≠ Sum.inl 0 ∧ i ≠ Sum.inr (Sum.inr 0)} := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Sum.inr_ne_inl, fun h => by simpa [e] using h⟩
    · rintro ⟨h1, h2⟩
      rcases i with i | j | i
      · exact absurd (congrArg Sum.inl (Subsingleton.elim i 0)) h1
      · exact ⟨j, rfl⟩
      · exact absurd (by rw [Subsingleton.elim i 0]) h2
  have hlevi : ∀ R : GL (Fin m) (ZMod 2),
      leviOne m R = CFSG.SeitzReduction.F4Pilot.coordEmbedGL (F := ZMod 2) e he R := by
    intro R
    refine Units.ext ?_
    rw [CFSG.SeitzReduction.F4Pilot.coe_coordEmbedGL]
    ext a b
    by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab
      rw [CFSG.SeitzReduction.F4Pilot.coordEmbedMat_apply_image he]
      rfl
    · rw [CFSG.SeitzReduction.F4Pilot.coordEmbedMat_apply_of_not_mem _ hab]
      rcases a with i | j | i <;> rcases b with i' | j' | i'
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · exact absurd ⟨⟨j, rfl⟩, ⟨j', rfl⟩⟩ hab
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
      · simp [leviOne, coe_levi, blk, Matrix.one_apply]
  rw [leviB, ← hrange]
  ext x
  constructor
  · rintro ⟨R, hR⟩
    rw [← hR, hlevi R]
    exact CFSG.SeitzReduction.F4Pilot.coordEmbedGL_mem_suppGL he R
  · intro hx
    obtain ⟨R, hR⟩ :=
      CFSG.SeitzReduction.F4Pilot.exists_coordEmbedGL_eq_of_mem_suppGL he hx
    exact ⟨R, (hlevi R).trans hR⟩


private theorem caBeta_mul_apply_of_row_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p q : κ} (hpq : p ≠ q) {N : Matrix κ κ (ZMod 2)} {a : κ}
    (hN : ∀ b, b ≠ p → b ≠ q → N a b = 0) (g : Matrix κ κ (ZMod 2)) (b : κ) :
    (N * g) a b = N a p * g p b + N a q * g q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add p q hpq]
  · intro c _ hc
    rw [hN c hc.1 hc.2, zero_mul]
  · simp
  · simp

private theorem caBeta_mul_apply_of_col_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p q : κ} (hpq : p ≠ q) {N : Matrix κ κ (ZMod 2)} {b : κ}
    (hN : ∀ a, a ≠ p → a ≠ q → N a b = 0) (g : Matrix κ κ (ZMod 2)) (a : κ) :
    (g * N) a b = g a p * N p b + g a q * N q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add p q hpq]
  · intro c _ hc
    rw [hN c hc.1 hc.2, mul_zero]
  · simp
  · simp

private theorem caBeta_sub_one_mul_self_of_cube_one :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2), M ^ 3 = 1 → M ≠ 1 →
      (M - 1) * M = 1 ∧ M * (M - 1) = 1 := by
  decide

private def caBeta_blk2 {κ : Type*} (p q : κ) (g : Matrix κ κ (ZMod 2)) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![g p p, g p q; g q p, g q q]

private theorem caBeta_blk2_zero_zero {κ : Type*} (p q : κ) (g : Matrix κ κ (ZMod 2)) :
    caBeta_blk2 p q g 0 0 = g p p := rfl

private theorem caBeta_blk2_zero_one {κ : Type*} (p q : κ) (g : Matrix κ κ (ZMod 2)) :
    caBeta_blk2 p q g 0 1 = g p q := rfl

private theorem caBeta_blk2_one_zero {κ : Type*} (p q : κ) (g : Matrix κ κ (ZMod 2)) :
    caBeta_blk2 p q g 1 0 = g q p := rfl

private theorem caBeta_blk2_one_one {κ : Type*} (p q : κ) (g : Matrix κ κ (ZMod 2)) :
    caBeta_blk2 p q g 1 1 = g q q := rfl

private theorem caBeta_blk2_mul_of_row_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p q : κ} (hpq : p ≠ q) {g₁ g₂ : Matrix κ κ (ZMod 2)}
    (h₁ : ∀ j, j ≠ p → j ≠ q → g₁ p j = 0 ∧ g₁ q j = 0) :
    caBeta_blk2 p q (g₁ * g₂) = caBeta_blk2 p q g₁ * caBeta_blk2 p q g₂ := by
  ext i j
  fin_cases i <;> fin_cases j
  · change caBeta_blk2 p q (g₁ * g₂) 0 0 =
      (caBeta_blk2 p q g₁ * caBeta_blk2 p q g₂) 0 0
    rw [caBeta_blk2_zero_zero]
    conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [caBeta_blk2_zero_zero, caBeta_blk2_zero_one, caBeta_blk2_one_zero]
    rw [caBeta_mul_apply_of_row_zero hpq (fun b hb1 hb2 => (h₁ b hb1 hb2).1) g₂ p]
  · change caBeta_blk2 p q (g₁ * g₂) 0 1 =
      (caBeta_blk2 p q g₁ * caBeta_blk2 p q g₂) 0 1
    rw [caBeta_blk2_zero_one]
    conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [caBeta_blk2_zero_zero, caBeta_blk2_zero_one, caBeta_blk2_one_one]
    rw [caBeta_mul_apply_of_row_zero hpq (fun b hb1 hb2 => (h₁ b hb1 hb2).1) g₂ q]
  · change caBeta_blk2 p q (g₁ * g₂) 1 0 =
      (caBeta_blk2 p q g₁ * caBeta_blk2 p q g₂) 1 0
    rw [caBeta_blk2_one_zero]
    conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [caBeta_blk2_one_zero, caBeta_blk2_one_one, caBeta_blk2_zero_zero]
    rw [caBeta_mul_apply_of_row_zero hpq (fun b hb1 hb2 => (h₁ b hb1 hb2).2) g₂ p]
  · change caBeta_blk2 p q (g₁ * g₂) 1 1 =
      (caBeta_blk2 p q g₁ * caBeta_blk2 p q g₂) 1 1
    rw [caBeta_blk2_one_one]
    conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [caBeta_blk2_one_zero, caBeta_blk2_one_one, caBeta_blk2_zero_one]
    rw [caBeta_mul_apply_of_row_zero hpq (fun b hb1 hb2 => (h₁ b hb1 hb2).2) g₂ q]

private theorem caBeta_blk2_pairGL {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}
    (hpq : p ≠ q) (M : GL (Fin 2) (ZMod 2)) :
    caBeta_blk2 p q (pairGL hpq M : Matrix κ κ (ZMod 2)) =
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    change caBeta_blk2 p q (pairGL hpq M : Matrix κ κ (ZMod 2)) _ _ =
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) _ _ <;>
    simp [caBeta_blk2_zero_zero, caBeta_blk2_zero_one, caBeta_blk2_one_zero,
      caBeta_blk2_one_one, coe_pairGL, CFSG.LieType.Steinberg.Sp.blockMat, hpq, hpq.symm]

private theorem caBeta_blk2_one {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}
    (hpq : p ≠ q) : caBeta_blk2 p q (1 : Matrix κ κ (ZMod 2)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    change caBeta_blk2 p q (1 : Matrix κ κ (ZMod 2)) _ _ =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) _ _ <;>
    simp [caBeta_blk2_zero_zero, caBeta_blk2_zero_one, caBeta_blk2_one_zero,
      caBeta_blk2_one_one, Matrix.one_apply, hpq, hpq.symm]

private theorem caBeta_blk2_sub_one_pairGL {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}
    (hpq : p ≠ q) (M : GL (Fin 2) (ZMod 2)) :
    caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) =
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    change caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) _ _ =
      ((M : Matrix (Fin 2) (Fin 2) (ZMod 2)) - 1) _ _ <;>
    simp [caBeta_blk2_zero_zero, caBeta_blk2_zero_one, caBeta_blk2_one_zero,
      caBeta_blk2_one_one, Matrix.sub_apply, coe_pairGL,
      CFSG.LieType.Steinberg.Sp.blockMat, Matrix.one_apply, hpq, hpq.symm]

private theorem caBeta_blockMat_apply_of_not {κ : Type*} [DecidableEq κ] {p q : κ}
    (hpq : p ≠ q) (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) {a b : κ}
    (h : (a ≠ p ∧ a ≠ q) ∨ (b ≠ p ∧ b ≠ q)) :
    CFSG.LieType.Steinberg.Sp.blockMat p q A a b = (1 : Matrix κ κ (ZMod 2)) a b := by
  rcases h with ⟨hap, haq⟩ | ⟨hbp, hbq⟩
  · simp [CFSG.LieType.Steinberg.Sp.blockMat, hap, haq]
  · by_cases hap : a = p
    · rw [show CFSG.LieType.Steinberg.Sp.blockMat p q A a b = 0 by
        simp [CFSG.LieType.Steinberg.Sp.blockMat, hap, hbp, hbq]]
      rw [Matrix.one_apply_ne (by rw [hap]; exact Ne.symm hbp)]
    · by_cases haq : a = q
      · rw [show CFSG.LieType.Steinberg.Sp.blockMat p q A a b = 0 by
          simp [CFSG.LieType.Steinberg.Sp.blockMat, haq, hbp, hbq, hpq.symm]]
        rw [Matrix.one_apply_ne (by rw [haq]; exact Ne.symm hbq)]
      · simp [CFSG.LieType.Steinberg.Sp.blockMat, hap, haq]

private theorem caBeta_blockMat_pp {κ : Type*} [DecidableEq κ] {p q : κ}
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    CFSG.LieType.Steinberg.Sp.blockMat p q A p p = A 0 0 := by
  simp [CFSG.LieType.Steinberg.Sp.blockMat]

private theorem caBeta_blockMat_pq {κ : Type*} [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    CFSG.LieType.Steinberg.Sp.blockMat p q A p q = A 0 1 := by
  simp [CFSG.LieType.Steinberg.Sp.blockMat, hpq, hpq.symm]

private theorem caBeta_blockMat_qp {κ : Type*} [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    CFSG.LieType.Steinberg.Sp.blockMat p q A q p = A 1 0 := by
  simp [CFSG.LieType.Steinberg.Sp.blockMat, hpq, hpq.symm]

private theorem caBeta_blockMat_qq {κ : Type*} [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    CFSG.LieType.Steinberg.Sp.blockMat p q A q q = A 1 1 := by
  simp [CFSG.LieType.Steinberg.Sp.blockMat, hpq, hpq.symm]

private theorem caBeta_blk2_mul_entry (A Ainv : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hMul : A * Ainv = 1) (i j : Fin 2) :
    A i 0 * Ainv 0 j + A i 1 * Ainv 1 j =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := by
  rw [← hMul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem caBeta_zero_off_of_mem_centralizer {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p q : κ} (hpq : p ≠ q) {M : GL (Fin 2) (ZMod 2)} (hM : orderOf M = 3)
    {g : GL κ (ZMod 2)}
    (hg : g ∈ Subgroup.centralizer ({pairGL hpq M} : Set (GL κ (ZMod 2)))) :
    (∀ j, j ≠ p → j ≠ q → (g : Matrix κ κ (ZMod 2)) p j = 0 ∧
      (g : Matrix κ κ (ZMod 2)) q j = 0) ∧
    (∀ i, i ≠ p → i ≠ q → (g : Matrix κ κ (ZMod 2)) i p = 0 ∧
      (g : Matrix κ κ (ZMod 2)) i q = 0) := by
  have hM3 : M ^ 3 = 1 := by
    rw [← hM]
    exact pow_orderOf_eq_one M
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM
    exact absurd hM (by decide)
  have hM3mat : (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) ^ 3 = 1 := by
    have h := congrArg (fun u : GL (Fin 2) (ZMod 2) =>
      (u : Matrix (Fin 2) (Fin 2) (ZMod 2))) hM3
    simpa [Units.val_pow_eq_pow_val] using h
  have hM1mat : (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 := by
    intro h
    exact hM1 (Units.ext h)
  have hBinv := caBeta_sub_one_mul_self_of_cube_one
    (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) hM3mat hM1mat
  have hcomm : (g : Matrix κ κ (ZMod 2)) * (pairGL hpq M : Matrix κ κ (ZMod 2)) =
      (pairGL hpq M : Matrix κ κ (ZMod 2)) * (g : Matrix κ κ (ZMod 2)) := by
    have h := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    simpa only [Units.val_mul] using congrArg (fun u : GL κ (ZMod 2) =>
      (u : Matrix κ κ (ZMod 2))) h
  have hNcomm : (g : Matrix κ κ (ZMod 2)) *
      ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) =
      ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) * (g : Matrix κ κ (ZMod 2)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcomm]
  have hN_zero : ∀ a b, (a ≠ p ∧ a ≠ q) ∨ (b ≠ p ∧ b ≠ q) →
      ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) a b = 0 := by
    intro a b h
    have hP : (pairGL hpq M : Matrix κ κ (ZMod 2)) a b =
        (1 : Matrix κ κ (ZMod 2)) a b := by
      rw [coe_pairGL]
      exact caBeta_blockMat_apply_of_not hpq (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) h
    rw [Matrix.sub_apply, hP, sub_self]
  constructor
  · intro j hj1 hj2
    have hcol : ∀ i, ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) i j = 0 :=
      fun i => hN_zero i j (Or.inr ⟨hj1, hj2⟩)
    have hgN_p : ((g : Matrix κ κ (ZMod 2)) *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) p j = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [hcol i, mul_zero]
    have hgN_q : ((g : Matrix κ κ (ZMod 2)) *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) q j = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [hcol i, mul_zero]
    have h1 : ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) p p *
        (g : Matrix κ κ (ZMod 2)) p j +
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) p q *
        (g : Matrix κ κ (ZMod 2)) q j = 0 := by
      rw [← caBeta_mul_apply_of_row_zero hpq
        (fun b hb1 hb2 => hN_zero p b (Or.inr ⟨hb1, hb2⟩))
        (g : Matrix κ κ (ZMod 2)) j]
      rw [hNcomm.symm]
      exact hgN_p
    have h2 : ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) q p *
        (g : Matrix κ κ (ZMod 2)) p j +
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) q q *
        (g : Matrix κ κ (ZMod 2)) q j = 0 := by
      rw [← caBeta_mul_apply_of_row_zero hpq
        (fun b hb1 hb2 => hN_zero q b (Or.inr ⟨hb1, hb2⟩))
        (g : Matrix κ κ (ZMod 2)) j]
      rw [hNcomm.symm]
      exact hgN_q
    have hBv : caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *ᵥ
        (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
          Fin 2 → ZMod 2) = 0 := by
      funext k
      fin_cases k
      · change (caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *ᵥ
          (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
            Fin 2 → ZMod 2)) 0 = 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, caBeta_blk2_zero_zero,
          caBeta_blk2_zero_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact h1
      · change (caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *ᵥ
          (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
            Fin 2 → ZMod 2)) 1 = 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, caBeta_blk2_one_zero,
          caBeta_blk2_one_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact h2
    have hMB : (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
        caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) = 1 := by
      rw [caBeta_blk2_sub_one_pairGL]
      exact hBinv.2
    have hv : (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
        Fin 2 → ZMod 2) = 0 := by
      calc _ = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
            (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
              Fin 2 → ZMod 2) := by rw [Matrix.one_mulVec]
        _ = ((M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
            caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) *ᵥ
            (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
              Fin 2 → ZMod 2) := by rw [hMB]
        _ = (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
            (caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *ᵥ
              (![(g : Matrix κ κ (ZMod 2)) p j, (g : Matrix κ κ (ZMod 2)) q j] :
                Fin 2 → ZMod 2)) := by rw [Matrix.mulVec_mulVec]
        _ = (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ 0 := by rw [hBv]
        _ = 0 := by rw [Matrix.mulVec_zero]
    exact ⟨by simpa using congrFun hv 0, by simpa using congrFun hv 1⟩
  · intro i hi1 hi2
    have hrow : ∀ j, ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) i j = 0 :=
      fun j => hN_zero i j (Or.inl ⟨hi1, hi2⟩)
    have hNg_p : (((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *
        (g : Matrix κ κ (ZMod 2))) i p = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hrow j, zero_mul]
    have hNg_q : (((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *
        (g : Matrix κ κ (ZMod 2))) i q = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hrow j, zero_mul]
    have h1 : (g : Matrix κ κ (ZMod 2)) i p *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) p p +
        (g : Matrix κ κ (ZMod 2)) i q *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) q p = 0 := by
      rw [← caBeta_mul_apply_of_col_zero hpq
        (fun a ha1 ha2 => hN_zero a p (Or.inl ⟨ha1, ha2⟩))
        (g : Matrix κ κ (ZMod 2)) i]
      rw [hNcomm]
      exact hNg_p
    have h2 : (g : Matrix κ κ (ZMod 2)) i p *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) p q +
        (g : Matrix κ κ (ZMod 2)) i q *
        ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) q q = 0 := by
      rw [← caBeta_mul_apply_of_col_zero hpq
        (fun a ha1 ha2 => hN_zero a q (Or.inl ⟨ha1, ha2⟩))
        (g : Matrix κ κ (ZMod 2)) i]
      rw [hNcomm]
      exact hNg_q
    have hBv : (![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
        Fin 2 → ZMod 2) ᵥ*
        caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) = 0 := by
      funext k
      fin_cases k
      · change ((![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
            Fin 2 → ZMod 2) ᵥ*
            caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) 0 = 0
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, caBeta_blk2_zero_zero,
          caBeta_blk2_one_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact h1
      · change ((![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
            Fin 2 → ZMod 2) ᵥ*
            caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) 1 = 0
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, caBeta_blk2_zero_one,
          caBeta_blk2_one_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact h2
    have hBM : caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *
        (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
      rw [caBeta_blk2_sub_one_pairGL]
      exact hBinv.1
    have hv : (![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
        Fin 2 → ZMod 2) = 0 := by
      calc _ = (![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
              Fin 2 → ZMod 2) ᵥ* (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
            rw [Matrix.vecMul_one]
        _ = (![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
              Fin 2 → ZMod 2) ᵥ*
              (caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1) *
                (M : Matrix (Fin 2) (Fin 2) (ZMod 2))) := by rw [hBM]
        _ = ((![(g : Matrix κ κ (ZMod 2)) i p, (g : Matrix κ κ (ZMod 2)) i q] :
              Fin 2 → ZMod 2) ᵥ*
              caBeta_blk2 p q ((pairGL hpq M : Matrix κ κ (ZMod 2)) - 1)) ᵥ*
              (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by rw [Matrix.vecMul_vecMul]
        _ = (0 : Fin 2 → ZMod 2) ᵥ* (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by rw [hBv]
        _ = 0 := by rw [Matrix.zero_vecMul]
    exact ⟨by simpa using congrFun hv 0, by simpa using congrFun hv 1⟩

private theorem caBeta_mul_blockMat_mem_suppGL {κ : Type*} [Fintype κ] [DecidableEq κ]
    {p q : κ} (hpq : p ≠ q) {g : Matrix κ κ (ZMod 2)}
    {A Ainv : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hrow : ∀ j, j ≠ p → j ≠ q → g p j = 0 ∧ g q j = 0)
    (hcol : ∀ i, i ≠ p → i ≠ q → g i p = 0 ∧ g i q = 0)
    (hA : A = caBeta_blk2 p q g) (hMul : A * Ainv = 1) :
    CFSG.SeitzReduction.SymplecticPilot.IsSuppMat {i | i ≠ p ∧ i ≠ q}
      (g * CFSG.LieType.Steinberg.Sp.blockMat p q Ainv) := by
  intro a b hab
  by_cases haT : a = p ∨ a = q
  · rcases haT with hap | haq
    · rw [hap]
      rw [caBeta_mul_apply_of_row_zero hpq (a := p)
        (fun c hc1 hc2 => (hrow c hc1 hc2).1)
        (CFSG.LieType.Steinberg.Sp.blockMat p q Ainv) b]
      by_cases hbT : b = p ∨ b = q
      · rcases hbT with hbp | hbq
        · rw [hbp]
          rw [← caBeta_blk2_zero_zero p q g, ← caBeta_blk2_zero_one p q g, ← hA,
            caBeta_blockMat_pp Ainv, caBeta_blockMat_qp hpq Ainv,
            caBeta_blk2_mul_entry A Ainv hMul 0 0]
          simp [Matrix.one_apply]
        · rw [hbq]
          rw [← caBeta_blk2_zero_zero p q g, ← caBeta_blk2_zero_one p q g, ← hA,
            caBeta_blockMat_pq hpq Ainv, caBeta_blockMat_qq hpq Ainv,
            caBeta_blk2_mul_entry A Ainv hMul 0 1]
          simp [Matrix.one_apply, hpq, hpq.symm]
      · have hbp : b ≠ p := fun h => hbT (Or.inl h)
        have hbq : b ≠ q := fun h => hbT (Or.inr h)
        rw [caBeta_blockMat_apply_of_not hpq Ainv (a := p) (b := b) (Or.inr ⟨hbp, hbq⟩),
          caBeta_blockMat_apply_of_not hpq Ainv (a := q) (b := b) (Or.inr ⟨hbp, hbq⟩),
          Matrix.one_apply_ne (Ne.symm hbp), Matrix.one_apply_ne (Ne.symm hbq)]
        simp [Matrix.one_apply_ne (Ne.symm hbp)]
    · rw [haq]
      rw [caBeta_mul_apply_of_row_zero hpq (a := q)
        (fun c hc1 hc2 => (hrow c hc1 hc2).2)
        (CFSG.LieType.Steinberg.Sp.blockMat p q Ainv) b]
      by_cases hbT : b = p ∨ b = q
      · rcases hbT with hbp | hbq
        · rw [hbp]
          rw [← caBeta_blk2_one_zero p q g, ← caBeta_blk2_one_one p q g, ← hA,
            caBeta_blockMat_pp Ainv, caBeta_blockMat_qp hpq Ainv,
            caBeta_blk2_mul_entry A Ainv hMul 1 0]
          simp [Matrix.one_apply, hpq, hpq.symm]
        · rw [hbq]
          rw [← caBeta_blk2_one_zero p q g, ← caBeta_blk2_one_one p q g, ← hA,
            caBeta_blockMat_pq hpq Ainv, caBeta_blockMat_qq hpq Ainv,
            caBeta_blk2_mul_entry A Ainv hMul 1 1]
          simp [Matrix.one_apply]
      · have hbp : b ≠ p := fun h => hbT (Or.inl h)
        have hbq : b ≠ q := fun h => hbT (Or.inr h)
        rw [caBeta_blockMat_apply_of_not hpq Ainv (a := p) (b := b) (Or.inr ⟨hbp, hbq⟩),
          caBeta_blockMat_apply_of_not hpq Ainv (a := q) (b := b) (Or.inr ⟨hbp, hbq⟩),
          Matrix.one_apply_ne (Ne.symm hbp), Matrix.one_apply_ne (Ne.symm hbq)]
        simp [Matrix.one_apply_ne (Ne.symm hbq)]
  · have hap : a ≠ p := fun h => haT (Or.inl h)
    have haq : a ≠ q := fun h => haT (Or.inr h)
    have hbT : b = p ∨ b = q := by
      by_contra hbT
      exact hab ⟨⟨hap, haq⟩, not_or.mp hbT⟩
    rcases hbT with hbp | hbq
    · rw [hbp]
      rw [caBeta_mul_apply_of_col_zero hpq (b := p)
        (fun c hc1 hc2 => by
          rw [caBeta_blockMat_apply_of_not hpq Ainv (a := c) (b := p)
              (Or.inl ⟨hc1, hc2⟩), Matrix.one_apply_ne hc1])
        g a]
      rw [(hcol a hap haq).1, (hcol a hap haq).2, zero_mul, zero_mul, zero_add,
        Matrix.one_apply_ne hap]
    · rw [hbq]
      rw [caBeta_mul_apply_of_col_zero hpq (b := q)
        (fun c hc1 hc2 => by
          rw [caBeta_blockMat_apply_of_not hpq Ainv (a := c) (b := q)
              (Or.inl ⟨hc1, hc2⟩), Matrix.one_apply_ne hc2])
        g a]
      rw [(hcol a hap haq).1, (hcol a hap haq).2, zero_mul, zero_mul, zero_add,
        Matrix.one_apply_ne haq]

private theorem caBeta_orderOf_betaTwo : orderOf betaTwo = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem caBeta_mem_zpowers_of_commute (y M : GL (Fin 2) (ZMod 2)) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hM : M * y = y * M) : M ∈ Subgroup.zpowers y := by
  have h : ∀ y : GL (Fin 2) (ZMod 2), y ^ 3 = 1 → y ≠ 1 →
      ∀ M : GL (Fin 2) (ZMod 2), M * y = y * M → M = 1 ∨ M = y ∨ M = y ^ 2 := by decide
  rcases h y hy3 hy1 M hM with rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _
  · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem centralizer_pairGL {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    {M : GL (Fin 2) (ZMod 2)} (hM : orderOf M = 3) :
    Subgroup.centralizer ({pairGL hpq M} : Set (GL κ (ZMod 2))) =
      suppGL (ZMod 2) {i | i ≠ p ∧ i ≠ q} ⊔ Subgroup.zpowers (pairGL hpq M) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hz := caBeta_zero_off_of_mem_centralizer hpq hM hg
    obtain ⟨hrow, hcol⟩ := hz
    have hg_inv : g⁻¹ ∈ Subgroup.centralizer ({pairGL hpq M} : Set (GL κ (ZMod 2))) :=
      (Subgroup.centralizer ({pairGL hpq M} : Set (GL κ (ZMod 2)))).inv_mem' hg
    have hz_inv := caBeta_zero_off_of_mem_centralizer hpq hM hg_inv
    obtain ⟨hrow_inv, hcol_inv⟩ := hz_inv
    have hM3 : M ^ 3 = 1 := by
      rw [← hM]
      exact pow_orderOf_eq_one M
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM
      exact absurd hM (by decide)
    set Mmat : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
      caBeta_blk2 p q (g : Matrix κ κ (ZMod 2)) with hMmat
    set MmatInv : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
      caBeta_blk2 p q ((g⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) with hMmatInv
    have hgg : (g : Matrix κ κ (ZMod 2)) *
        ((g⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgig : ((g⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) *
        (g : Matrix κ κ (ZMod 2)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hMmat_mul : Mmat * MmatInv = 1 := by
      rw [hMmat, hMmatInv]
      have h := caBeta_blk2_mul_of_row_zero hpq (g₁ := (g : Matrix κ κ (ZMod 2)))
        (g₂ := ((g⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2))) hrow
      rw [hgg, caBeta_blk2_one hpq] at h
      exact h.symm
    have hMmatInv_mul : MmatInv * Mmat = 1 := by
      rw [hMmat, hMmatInv]
      have h := caBeta_blk2_mul_of_row_zero hpq
        (g₁ := ((g⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)))
        (g₂ := (g : Matrix κ κ (ZMod 2))) hrow_inv
      rw [hgig, caBeta_blk2_one hpq] at h
      exact h.symm
    set MGL : GL (Fin 2) (ZMod 2) := ⟨Mmat, MmatInv, hMmat_mul, hMmatInv_mul⟩ with hMGL
    have hProw : ∀ j, j ≠ p → j ≠ q →
        (pairGL hpq M : Matrix κ κ (ZMod 2)) p j = 0 ∧
          (pairGL hpq M : Matrix κ κ (ZMod 2)) q j = 0 := by
      intro j hj1 hj2
      constructor
      · rw [coe_pairGL]
        rw [caBeta_blockMat_apply_of_not hpq (M : Matrix (Fin 2) (Fin 2) (ZMod 2))
          (a := p) (b := j) (Or.inr ⟨hj1, hj2⟩)]
        exact Matrix.one_apply_ne (Ne.symm hj1)
      · rw [coe_pairGL]
        rw [caBeta_blockMat_apply_of_not hpq (M : Matrix (Fin 2) (Fin 2) (ZMod 2))
          (a := q) (b := j) (Or.inr ⟨hj1, hj2⟩)]
        exact Matrix.one_apply_ne (Ne.symm hj2)
    have hcomm : (g : Matrix κ κ (ZMod 2)) * (pairGL hpq M : Matrix κ κ (ZMod 2)) =
        (pairGL hpq M : Matrix κ κ (ZMod 2)) * (g : Matrix κ κ (ZMod 2)) := by
      have h := (Subgroup.mem_centralizer_singleton_iff.mp hg)
      simpa only [Units.val_mul] using congrArg (fun u : GL κ (ZMod 2) =>
        (u : Matrix κ κ (ZMod 2))) h
    have hMGLcomm : MGL * M = M * MGL := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      change Mmat * (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
        (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) * Mmat
      rw [hMmat]
      have h1 := caBeta_blk2_mul_of_row_zero hpq (g₁ := (g : Matrix κ κ (ZMod 2)))
        (g₂ := (pairGL hpq M : Matrix κ κ (ZMod 2))) hrow
      have h2 := caBeta_blk2_mul_of_row_zero hpq
        (g₁ := (pairGL hpq M : Matrix κ κ (ZMod 2)))
        (g₂ := (g : Matrix κ κ (ZMod 2))) hProw
      rw [caBeta_blk2_pairGL hpq M] at h1 h2
      have h := congrArg (caBeta_blk2 p q) hcomm
      rw [h1, h2] at h
      exact h
    have hMGL_zp : MGL ∈ Subgroup.zpowers M :=
      caBeta_mem_zpowers_of_commute M MGL hM3 hM1 hMGLcomm
    have hP'zp : pairGL hpq MGL ∈ Subgroup.zpowers (pairGL hpq M) := by
      rw [Subgroup.mem_zpowers_iff] at hMGL_zp ⊢
      obtain ⟨k, hk⟩ := hMGL_zp
      exact ⟨k, by rw [← map_zpow (pairGL hpq) M k, hk]⟩
    set h : GL κ (ZMod 2) := g * (pairGL hpq MGL)⁻¹ with hh
    have hh_eq : h * pairGL hpq MGL = g := by
      rw [hh, mul_assoc, inv_mul_cancel, mul_one]
    have hh_mem : h ∈ suppGL (ZMod 2) {i | i ≠ p ∧ i ≠ q} := by
      rw [CFSG.SeitzReduction.SymplecticPilot.mem_suppGL]
      have hP'inv : (pairGL hpq MGL)⁻¹ = pairGL hpq MGL⁻¹ :=
        (map_inv (pairGL hpq) MGL).symm
      have hMGLinv : ((MGL⁻¹ : GL (Fin 2) (ZMod 2)) :
          Matrix (Fin 2) (Fin 2) (ZMod 2)) = MmatInv := by
        rw [hMGL]
        rfl
      rw [hh, Units.val_mul, hP'inv, coe_pairGL, hMGLinv]
      exact caBeta_mul_blockMat_mem_suppGL hpq hrow hcol hMmat hMmat_mul
    rw [← hh_eq]
    exact Subgroup.mul_mem_sup hh_mem hP'zp
  · refine sup_le ?_ ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hST : Disjoint {i : κ | i ≠ p ∧ i ≠ q} {i : κ | i = p ∨ i = q} := by
        rw [Set.disjoint_left]
        intro a ha hb
        rcases hb with rfl | rfl
        · exact ha.1 rfl
        · exact ha.2 rfl
      have hP : pairGL hpq M ∈ suppGL (ZMod 2) {i : κ | i = p ∨ i = q} := by
        rw [CFSG.SeitzReduction.SymplecticPilot.mem_suppGL]
        intro a b hab
        rw [coe_pairGL]
        exact caBeta_blockMat_apply_of_not hpq (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (by
          rcases not_and_or.mp hab with ha | hb
          · exact Or.inl (not_or.mp ha)
          · exact Or.inr (not_or.mp hb))
      exact (CFSG.SeitzReduction.OmegaPilot.commute_of_mem_suppGL_of_disjoint hST hg hP).eq
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
theorem centralizer_betaStd (m : ℕ) :
    Subgroup.centralizer ({betaStd m} : Set (GL (BlkIdx 1 m) (ZMod 2))) =
      leviB m ⊔ Subgroup.zpowers (betaStd m) := by
  have h := centralizer_pairGL (κ := BlkIdx 1 m) (p := Sum.inl 0)
    (q := Sum.inr (Sum.inr 0)) (inl_ne_inr_inr m) (M := betaTwo) caBeta_orderOf_betaTwo
  rw [← leviB_eq_suppGL m] at h
  simpa [betaStd] using h

end CFSG.StandardType.FF81.CentA

end
