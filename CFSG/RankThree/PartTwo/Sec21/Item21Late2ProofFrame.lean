module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProof2119
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec21.Item21LateProofTypeTwo
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate2197
public import Certificates.Certificate3017
public import Certificates.Certificate3084
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3169
public import Certificates.Certificate3172
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Sec11.Data
import Certificates.Certificate3139

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)
open CFSG.RankThree.PartTwo.Sec4 renaming entry_eq_zero_of_commute_diagonal →
  entry_eq_zero_of_commute_diagonal'
open CFSG.Assembly.RankThreeEven (projImage projSL)

section Matrices

variable {K : Type} [Field K]

@[expose] def swapOT : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapOT :
    ((swapOT : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem swapOT_mul_diagUnits (a b c : Kˣ) :
    swapOT * diagUnits a b c = diagUnits a c b * swapOT := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapOT, coe_diagUnits, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem det_swapOT (h2 : (2 : K) = 0) :
    ((swapOT : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_swapOT, det_fin_three]
  simp
  linear_combination -h2

theorem swapOT_mul_scalar (l : Kˣ) :
    swapOT * GeneralLinearGroup.scalar (Fin 3) l = GeneralLinearGroup.scalar (Fin 3) l * swapOT :=
  (SL3Lines.scalar_mul_comm l swapOT).symm

theorem swapOT_conj (l s t : Kˣ) :
    swapOT * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * swapOT⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 t s := by
  rw [← mul_assoc, swapOT_mul_scalar, mul_assoc _ swapOT, swapOT_mul_diagUnits, mul_assoc,
    mul_assoc, mul_inv_cancel, mul_one]

theorem inv_scalar_mul_diagUnits (l s t : Kˣ) :
    (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l⁻¹ * diagUnits 1 s⁻¹ t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, Sec4.scalar_diagUnits_mul, mul_inv_cancel, mul_inv_cancel,
    mul_inv_cancel, map_one, one_mul, SL3Lines.diagUnits_one_one_one]

theorem scalar_apply_self' (l : Kˣ) (i : Fin 3) :
    ((GeneralLinearGroup.scalar (Fin 3) l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = l := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem trace_scalar_mul_diagUnits (l s t : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).trace = (l : K) * (1 + s + t) := by
  rw [Sec4.scalar_mul_diagUnits_eq, Sec4.coe_diagHom, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Units.val_mul]
  ring

theorem det_scalar_mul_diagUnits (l s t : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = (l : K) ^ 3 * s * t := by
  rw [Sec4.scalar_mul_diagUnits_eq, Sec4.coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Units.val_mul]
  ring

theorem trace_det_conj_mul_scalar (R Y : GL (Fin 3) K) (u : Kˣ) :
    ((R * Y * R⁻¹ * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).trace = (u : K) * (Y : Matrix (Fin 3) (Fin 3) K).trace ∧
      ((R * Y * R⁻¹ * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = (u : K) ^ 3 * (Y : Matrix (Fin 3) (Fin 3) K).det := by
  constructor
  · rw [Sec4.trace_mul_scalar]
    congr 1
    have := Sec4.trace_inv_conj R⁻¹ Y
    rwa [inv_inv] at this
  · have hdetR : (R : Matrix (Fin 3) (Fin 3) K).det *
        ((R⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Fin.prod_const, Units.val_mul, Units.val_mul, Matrix.det_mul,
      Matrix.det_mul]
    linear_combination ((u : K) ^ 3 * (Y : Matrix (Fin 3) (Fin 3) K).det) * hdetR

theorem cases_of_trace_det (h2 : (2 : K) = 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {ρ s t : K} (hs : s = 1 ∨ s = τ ∨ s = τ ^ 2) (ht : t = 1 ∨ t = τ ∨ t = τ ^ 2)
    (e1 : ρ * (1 + s + t) = 1 + s ^ 2 + t ^ 2) (e2 : ρ ^ 3 * s ^ 2 * t ^ 2 = 1) :
    (s = 1 ∧ t = 1) ∨ (s = τ ∧ t = τ ^ 2) ∨ (s = τ ^ 2 ∧ t = τ) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hne2 : τ ^ 2 ≠ 1 := fun h => hτ1 (by linear_combination -(τ) * h + hτ)
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;> rw [hs, ht] at e1 e2
  · exact Or.inl ⟨hs, ht⟩
  ·
    exfalso
    have hρ : ρ = τ := mul_right_cancel₀ hτ0 (by linear_combination e1 - ρ * h2 + h2)
    rw [hρ] at e2
    exact hne2 (by linear_combination e2 - τ ^ 2 * hτ)
  ·
    exfalso
    have h1 : ρ * τ ^ 2 = τ := by linear_combination e1 - ρ * h2 + h2 + τ * hτ
    have hρ : ρ = τ ^ 2 := by linear_combination τ * h1 - ρ * hτ
    rw [hρ] at e2
    exact hτ1 (by linear_combination e2 - τ * (τ ^ 6 + τ ^ 3 + 1) * hτ)
  ·
    exfalso
    have hρ : ρ = τ := mul_right_cancel₀ hτ0 (by linear_combination e1 - ρ * h2 + h2)
    rw [hρ] at e2
    exact hne2 (by linear_combination e2 - τ ^ 2 * hτ)
  ·
    exfalso
    have hρ : ρ = 1 := by linear_combination e1 - ρ * τ * h2 + τ ^ 2 * h2
    rw [hρ] at e2
    exact hτ1 (by linear_combination e2 - τ * hτ)
  · exact Or.inr (Or.inl ⟨hs, ht⟩)
  ·
    exfalso
    have h1 : ρ * τ ^ 2 = τ := by linear_combination e1 - ρ * h2 + h2 + τ * hτ
    have hρ : ρ = τ ^ 2 := by linear_combination τ * h1 - ρ * hτ
    rw [hρ] at e2
    exact hτ1 (by linear_combination e2 - τ * (τ ^ 6 + τ ^ 3 + 1) * hτ)
  · exact Or.inr (Or.inr ⟨hs, ht⟩)
  ·
    exfalso
    have hρ : ρ = 1 := by linear_combination e1 - ρ * τ ^ 2 * h2 + τ ^ 4 * h2
    rw [hρ] at e2
    exact hne2 (by linear_combination e2 - τ ^ 2 * (τ ^ 3 + 1) * hτ)

theorem eq_of_conj_inv (h2 : (2 : K) = 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {l s t : Kˣ} (hs : (s : K) ^ 3 = 1) (ht : (t : K) ^ 3 = 1) {R : GL (Fin 3) K} {u : Kˣ}
    (h : R * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * R⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) u =
      (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)⁻¹) :
    ((s : K) = 1 ∧ (t : K) = 1) ∨ ((s : K) = τ ∧ (t : K) = τ ^ 2) ∨
      ((s : K) = τ ^ 2 ∧ (t : K) = τ) := by
  obtain ⟨htr, hdet⟩ := trace_det_conj_mul_scalar R
    (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) u
  rw [h, inv_scalar_mul_diagUnits, trace_scalar_mul_diagUnits,
    trace_scalar_mul_diagUnits] at htr
  rw [h, inv_scalar_mul_diagUnits, det_scalar_mul_diagUnits, det_scalar_mul_diagUnits] at hdet
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  simp only [Units.val_inv_eq_inv_val] at htr hdet
  have hsi : (s : K)⁻¹ = (s : K) ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hs)).symm
  have hti : (t : K)⁻¹ = (t : K) ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ht)).symm
  rw [hsi, hti] at htr hdet
  have hl1 : (l : K)⁻¹ * l = 1 := inv_mul_cancel₀ hl0
  have hl3 : (l : K)⁻¹ ^ 3 * (l : K) ^ 3 = 1 := by
    rw [← mul_pow, hl1, one_pow]
  have e1 : ((u : K) * (l : K) ^ 2) * (1 + s + t) = 1 + (s : K) ^ 2 + (t : K) ^ 2 := by
    linear_combination -(l : K) * htr + (1 + (s : K) ^ 2 + (t : K) ^ 2) * hl1
  have e2 : ((u : K) * (l : K) ^ 2) ^ 3 * (s : K) ^ 2 * (t : K) ^ 2 = 1 := by
    linear_combination -(l : K) ^ 3 * s * t * hdet + (s : K) ^ 3 * (t : K) ^ 3 * hl3 +
      (t : K) ^ 3 * hs + ht
  exact cases_of_trace_det h2 hτ hτ1 (Sec4.cube_root_cases hτ hτ1 hs)
    (Sec4.cube_root_cases hτ hτ1 ht) e1 e2

theorem cycThree_mul_diagUnits (a b c : Kˣ) :
    Sec4.cycThree * diagUnits a b c = diagUnits c a b * Sec4.cycThree := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Sec4.coe_cycThree, coe_diagUnits, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem det_cycThree : ((Sec4.cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Sec4.coe_cycThree, det_fin_three]
  simp

theorem cycThree_pow_three : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem cycThree_conj (l s t : Kˣ) :
    Sec4.cycThree * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * Sec4.cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (l * t) * diagUnits 1 t⁻¹ (s * t⁻¹) := by
  rw [← mul_assoc, ← SL3Lines.scalar_mul_comm l Sec4.cycThree, mul_assoc _ Sec4.cycThree,
    cycThree_mul_diagUnits, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, coe_diagUnits, coe_diagUnits,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [Units.val_mul]
  field_simp

theorem commute_diagonal_of_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {N : Matrix (Fin 3) (Fin 3) K}
    (hN : N * diagonal ![1, τ, τ ^ 2] = diagonal ![1, τ, τ ^ 2] * N) (d : Fin 3 → K) :
    N * diagonal d = diagonal d * N := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h01 : (1 : K) ≠ τ := Ne.symm hτ1
  have h02 : (1 : K) ≠ τ ^ 2 := by
    intro h
    exact hτ1 (by linear_combination τ * h + hτ)
  have h12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have h' : τ * (τ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hτ0)
  have hNd : N = diagonal fun i => N i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h01)
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h02)
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h01.symm)
      · exact absurd rfl hij
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h12)
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h02.symm)
      · exact entry_eq_zero_of_commute_diagonal' hN (by simpa using h12.symm)
      · exact absurd rfl hij
  rw [hNd, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Matrices

section PGL

variable {K : Type} [Field K]

theorem mk_eq_one_of_mem_statedScalars {g : GL (Fin 3) K} (hg : g ∈ StatedScalars (Fin 3) K) :
    ProjGenLinGroup.mk g = 1 := by
  obtain ⟨u, rfl⟩ := hg
  exact ProjGenLinGroup.mk_scalar u

theorem diagTau_eq {τ : Kˣ} (hτ : (τ : K) ^ 3 = 1) :
    Sec4.diagTau hτ = GeneralLinearGroup.scalar (Fin 3) τ * diagUnits 1 τ (τ ^ 2) := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits,
    diagonal_mul_diagonal, Sec4.coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, pow_two]
  linear_combination -hτ

theorem mk_swapOT_conj (l : Kˣ) {τ : Kˣ} (hτ : τ ^ 3 = 1) :
    ProjGenLinGroup.mk (swapOT * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 τ (τ ^ 2)) *
        swapOT⁻¹) =
      (ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 τ (τ ^ 2)))⁻¹ := by
  rw [swapOT_conj, ← map_inv, inv_scalar_mul_diagUnits, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨l⁻¹ * l⁻¹, ?_⟩
  have h1 : τ⁻¹ = τ ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hτ
  have h2 : (τ ^ 2)⁻¹ = τ := by rw [← h1, inv_inv]
  rw [h1, h2, mul_assoc, ← SL3Lines.scalar_mul_comm, ← mul_assoc, ← map_mul]
  congr 2
  group

theorem mk_eq_of_conj_eq {π : Bool} {p f : ℕ} (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {N N' : GL (Fin 3) K}
    (h : ∀ s ∈ Sec4.slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk N * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk N)⁻¹ =
        ProjGenLinGroup.mk N' * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk N')⁻¹) :
    ProjGenLinGroup.mk N = ProjGenLinGroup.mk N' := by
  have hc : ∀ s ∈ Sec4.slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk (N'⁻¹ * N) * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk (N'⁻¹ * N) := by
    intro s hs
    rw [map_mul, map_inv]
    calc (ProjGenLinGroup.mk N')⁻¹ * ProjGenLinGroup.mk N * ProjGenLinGroup.mk s
        = (ProjGenLinGroup.mk N')⁻¹ * (ProjGenLinGroup.mk N * ProjGenLinGroup.mk s *
            (ProjGenLinGroup.mk N)⁻¹) * ProjGenLinGroup.mk N := by group
      _ = (ProjGenLinGroup.mk N')⁻¹ * (ProjGenLinGroup.mk N' * ProjGenLinGroup.mk s *
            (ProjGenLinGroup.mk N')⁻¹) * ProjGenLinGroup.mk N := by rw [h s hs]
      _ = ProjGenLinGroup.mk s * ((ProjGenLinGroup.mk N')⁻¹ * ProjGenLinGroup.mk N) := by group
  have h1 := mk_eq_one_of_mem_statedScalars (Sec13.mem_statedScalars_of_commute_mk hK hq hq2 hc)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

end PGL

section TypeOne

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_inner {L : Subgroup G} {d : G} (hdL : d ∈ L)
    (hx : d ∈ Subgroup.normalizer (L : Set G)) (z : lBar L) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hx⟩) z =
      ((⟨d, hdL⟩ : L) : lBar L) * z * ((⟨d, hdL⟩ : L) : lBar L)⁻¹ := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

theorem two_eq_zero_of_piField {f : ℕ} {K : Type} [Field K] (hK : Sec4.PiField true 2 f K) :
    (2 : K) = 0 := by
  have : Finite K := hK.finite
  let _ := Fintype.ofFinite K
  have hKcard : Nat.card K = 2 ^ f := hK.card
  have : CharP K 2 := by
    obtain ⟨k, hkp, hk⟩ := FiniteField.card K (ringChar K)
    rw [Fintype.card_eq_nat_card, hKcard] at hk
    have h2 : 2 ∣ ringChar K ^ (k : ℕ) := hk ▸ dvd_pow_self 2 (by have := hK.one_le; omega)
    exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hkp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  exact_mod_cast CharP.cast_eq_zero K 2

omit [Finite G] in
theorem coe_e_eq_mk_of_inner {L : Subgroup G} {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : lBar L ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (x : lBar L) (y : GL (Fin 3) K)
    (h : ∀ z : lBar L, ((e (x * z * x⁻¹) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    (e x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y := by
  obtain ⟨s₀, hs₀, hs₀x⟩ := (e x).2
  have hc : ∀ s ∈ Sec4.slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk (y⁻¹ * s₀) * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk (y⁻¹ * s₀) := by
    intro s hs
    set z := e.symm ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := h z
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hez,
      ← hs₀x] at h1
    rw [map_mul, map_inv]
    calc (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk s₀ * ProjGenLinGroup.mk s
        = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk s₀ * ProjGenLinGroup.mk s *
            (ProjGenLinGroup.mk s₀)⁻¹) * ProjGenLinGroup.mk s₀ := by group
      _ = (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk s *
            (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk s₀ := by rw [h1]
      _ = ProjGenLinGroup.mk s * ((ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk s₀) := by group
  have hsc := Sec13.mem_statedScalars_of_commute_mk hK hq hq2 hc
  have h1 := mk_eq_one_of_mem_statedScalars hsc
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [← hs₀x]
  exact h1.symm

theorem exists_conj_inv_of_inducesTypeOn_one {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar L ≃* projSL 3 (GaloisField 2 n)) {d : G} (hdL : d ∈ L)
    (hd : Sec4.InducesTypeOn L d 1) :
    ∃ m : lBar L, m * ((⟨d, hdL⟩ : L) : lBar L) * m⁻¹ = ((⟨d, hdL⟩ : L) : lBar L)⁻¹ := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, -, hy1, hact⟩ := hd
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hK.prime hK.one_le
    (by omega) hq hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have h2 : (2 : K) = 0 := two_eq_zero_of_piField hK
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
  set D' : lBar L := ((⟨d, hdL⟩ : L) : lBar L) with hD'
  have hey : (e D' : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y := by
    refine coe_e_eq_mk_of_inner hK hq hq2 e D' y fun z => ?_
    rw [← thetaQuotMulAut_inner hdL hx z]
    exact hact z
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := hy1
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hτ)
  have hzs := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hmkz : ProjGenLinGroup.mk z = 1 := mk_eq_one_of_mem_statedScalars hzs
  set X := GeneralLinearGroup.scalar (Fin 3) τu * diagUnits 1 τu (τu ^ 2) with hX
  have hXD : Sec4.diagTau hτ = X := diagTau_eq (τ := τu) hτ
  have hyz : y * z = g * X * g⁻¹ := by
    rw [← hXD, ← hD]
    group
  set r := g * swapOT * g⁻¹ with hr
  have hrSL : r ∈ Sec4.slPi true 3 (2 ^ f) K := by
    rw [Sec4.mem_slPi_true, hr, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      det_swapOT h2, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]
  have hry : ProjGenLinGroup.mk r * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk r)⁻¹ =
      (ProjGenLinGroup.mk y)⁻¹ := by
    have hmy : ProjGenLinGroup.mk y = ProjGenLinGroup.mk (g * X * g⁻¹) := by
      rw [← hyz, map_mul, hmkz, mul_one]
    have hP : ProjGenLinGroup.mk (swapOT * X * swapOT⁻¹) = (ProjGenLinGroup.mk X)⁻¹ :=
      mk_swapOT_conj (K := K) τu hτu3
    have e1 : r * (g * X * g⁻¹) * r⁻¹ = g * (swapOT * X * swapOT⁻¹) * g⁻¹ := by
      rw [hr]
      group
    calc ProjGenLinGroup.mk r * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk r)⁻¹
        = ProjGenLinGroup.mk (r * (g * X * g⁻¹) * r⁻¹) := by
          rw [hmy, ← map_inv, ← map_mul, ← map_mul]
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk (swapOT * X * swapOT⁻¹) *
            (ProjGenLinGroup.mk g)⁻¹ := by rw [e1, map_mul, map_mul, map_inv]
      _ = (ProjGenLinGroup.mk g * ProjGenLinGroup.mk X * (ProjGenLinGroup.mk g)⁻¹)⁻¹ := by
          rw [hP]
          group
      _ = (ProjGenLinGroup.mk y)⁻¹ := by
          rw [hmy, ← map_inv ProjGenLinGroup.mk g, ← map_mul, ← map_mul]
  set m := e.symm ⟨ProjGenLinGroup.mk r, Subgroup.mem_map_of_mem _ hrSL⟩ with hm
  have hem : (e m : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk r := by
    rw [hm, MulEquiv.apply_symm_apply]
  refine ⟨m, e.injective (Subtype.ext ?_)⟩
  rw [map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_inv, hem, hey]
  exact hry

end TypeOne

section Frame

variable {G : Type} [Group G] [Finite G]

theorem frame_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G}
    (hcfg : Config2119 G A E U c L) :
    c ∉ L ∧ ∃ d₀ ∈ A ⊓ L, d₀ ≠ 1 ∧ Sec4.InducesTypeOn L d₀ 1 ∧
      (∀ d ∈ A ⊓ L, d ≠ 1 → Sec4.InducesTypeOn L d 1 → d = d₀ ∨ d = d₀⁻¹) ∧
      (∀ x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (A : Set G),
        x * d₀ * x⁻¹ = d₀ ∨ x * d₀ * x⁻¹ = d₀⁻¹) ∧
      (∀ x ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (A : Set G), x * d₀ * x⁻¹ = d₀ ∨ x * d₀ * x⁻¹ = d₀⁻¹) ∧
      (Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (∃ w ∈ L ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 ∧ w * d₀ * w⁻¹ = d₀ ∧
        (∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers d₀) ∧ ∃ a ∈ A, w * a * w⁻¹ ≠ a) ∧
      ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G), t * d₀ * t⁻¹ = d₀⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hpair, ⟨n, hn0, hev, ⟨eL⟩⟩, hC, h27, ⟨eS⟩⟩ := hcfg
  have hn : 2 ≤ n := by obtain ⟨k, hk⟩ := hev; omega
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
    hpair.mem_S.1.2.1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : ∀ a ∈ A, a ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h3 c hcA) hc1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, hc3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun y hy => h3 y hy.1
  have hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAL, hCA]
  set T : Subgroup.normalizer (L : Set G) →* MulAut (lBar L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hT
  have hTinner : ∀ (l₀ : G) (hl₀ : l₀ ∈ L) (z : lBar L),
      T ⟨l₀, Subgroup.le_normalizer hl₀⟩ z =
        ((⟨l₀, hl₀⟩ : L) : lBar L) * z * ((⟨l₀, hl₀⟩ : L) : lBar L)⁻¹ :=
    fun l₀ hl₀ z => thetaQuotMulAut_inner hl₀ _ z
  obtain ⟨-, -, hN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hθ3 : ∀ l : L, l ∈ aschbacherSolvableCore 3 L → ∀ k : ℕ, l ^ 3 ^ k = 1 → l = 1 := by
    intro l hl k hlk
    have h1 := orderOf_dvd_natCard (⟨l, hl⟩ : aschbacherSolvableCore 3 L)
    have h2 : orderOf (⟨l, hl⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hlk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact congrArg Subtype.val hj
    · exfalso
      apply hN3
      rw [hj] at h1
      exact (dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h1
  have hinjAL : ∀ (b b' : G) (hb : b ∈ A ⊓ L) (hb' : b' ∈ A ⊓ L),
      ((⟨b, hb.2⟩ : L) : lBar L) = ((⟨b', hb'.2⟩ : L) : lBar L) → b = b' := by
    intro b b' hb hb' h
    rw [QuotientGroup.eq] at h
    have h1 := hθ3 _ h 1 (Subtype.ext (by
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      exact h3 _ (A.mul_mem (A.inv_mem hb.1) hb'.1)))
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    exact (inv_mul_eq_one.mp h2)
  have hZ : Subgroup.center (lBar L) = ⊥ := by
    have := Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 n)
    have hsimp : IsSimpleGroup (lBar L) := eL.isSimpleGroup
    exact Item21Early2Proof.center_eq_bot_of_isSimpleGroup_of_not_prime (by
      obtain ⟨r, hr, hcard⟩ := Item21LateProof.card_projSL3_eq n
      rw [Nat.card_congr eL.toEquiv, hcard]
      refine Item21Early2Proof.not_prime_of_four_dvd ?_
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) r)
  have hcL : c ∉ L := by
    intro hcL
    have hcZ : ((⟨c, hcL⟩ : L) : lBar L) ∈ Subgroup.center (lBar L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2))
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcZ
    exact hc1 (congrArg Subtype.val (hθ3 _ hcZ 1
      (Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact h3 c hcA))))
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, hconj'⟩ := hC
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    (by omega) hmod hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have h2 : (2 : K) = 0 := two_eq_zero_of_piField hPi
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  have hτ₀0 : τ₀ ≠ 0 := by
    rintro rfl
    norm_num at hτ₀
  set τu : Kˣ := Units.mk0 τ₀ hτ₀0 with hτudef
  have hτuv : (τu : K) = τ₀ := rfl
  have hτu3 : τu ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hτuv, hτ₀, Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ₀1 (by rw [← hτuv, h, Units.val_one])
  set ψ : lBar L →* ProjGenLinGroup (Fin 3) K :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype_injective.comp e.injective
  have hψe : ∀ z, ψ z = (e z : ProjGenLinGroup (Fin 3) K) := fun z => rfl
  have hyA : ∀ (a : G) (ha : a ∈ A), ∃ y ∈ D, ∀ z,
      ψ (T ⟨a, hAL ha⟩ z) = ProjGenLinGroup.mk y * ψ z * (ProjGenLinGroup.mk y)⁻¹ := by
    intro a ha
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩)
    exact ⟨y, hyD, fun z => hy z⟩
  obtain ⟨g, -, hdiag, hsurj⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  set D₁ : GL (Fin 3) K := diagUnits 1 τu (τu ^ 2) with hD₁
  set M : GL (Fin 3) K := g * D₁ * g⁻¹ with hM
  have hMSL : M ∈ Sec4.slPi true 3 (2 ^ f) K := by
    rw [Sec4.mem_slPi_true, hM, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      hD₁, coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_one, one_mul, Units.val_pow_eq_pow_val]
    rw [← pow_succ', hτuv, hτ₀, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one]
  have hdiagcomm : ∀ (y : GL (Fin 3) K) (l s t : Kˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t → y * M = M * y := by
    intro y l s t hy
    have hY : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
      rw [← hy]
      group
    have hc : (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * D₁ =
        D₁ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) := by
      rw [hD₁, mul_assoc, Sec4.diagUnits_mul, ← mul_assoc, ← SL3Lines.scalar_mul_comm l,
        mul_assoc, Sec4.diagUnits_mul, mul_comm (1 : Kˣ), mul_comm s, mul_comm t]
    rw [hY, hM]
    calc g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ * (g * D₁ * g⁻¹)
        = g * ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * D₁) * g⁻¹ := by group
      _ = g * (D₁ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)) * g⁻¹ := by rw [hc]
      _ = g * D₁ * g⁻¹ * (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹) := by
          group
  set ζ : projImage (Sec4.slPi true 3 (2 ^ f) K) :=
    ⟨ProjGenLinGroup.mk M, Subgroup.mem_map_of_mem _ hMSL⟩ with hζ
  set wb : lBar L := e.symm ζ with hwb
  have hψwb : ψ wb = ProjGenLinGroup.mk M := by
    rw [hψe, hwb, MulEquiv.apply_symm_apply]
  have hfix : ∀ (x : G) (hx : x ∈ A), T ⟨x, hAL hx⟩ wb = wb := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := hyA x hx
    obtain ⟨l, s, t, -, -, hyg⟩ := hdiag y hyD
    apply hψinj
    rw [hy, hψwb, ← map_inv, ← map_mul, ← map_mul, hdiagcomm y l s t hyg, mul_inv_cancel_right]
  have hM3 : M ^ 3 = 1 := by
    have hD3 : D₁ ^ 3 = 1 := by
      have h6 : (τu ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτu3, one_pow]
      rw [hD₁, pow_three, Sec4.diagUnits_mul, Sec4.diagUnits_mul, ← pow_three, ← pow_three,
        ← pow_three, one_pow, hτu3, h6, SL3Lines.diagUnits_one_one_one]
    rw [hM, conj_pow, hD3, mul_one, mul_inv_cancel]
  have hwb3 : wb ^ 3 = 1 := by
    apply hψinj
    rw [map_pow, hψwb, ← map_pow, hM3, map_one, map_one]
  obtain ⟨n₀, hn₀A, hn₀w⟩ := Sec13.Item138Proof.exists_mem_of_fixed hAL hAe hmax hwb3 hfix
  set d₀ : G := (n₀ : G) with hd₀
  have hd₀L : d₀ ∈ L := n₀.2
  have hd₀B : d₀ ∈ A ⊓ L := ⟨hn₀A, hd₀L⟩
  have hd₀bar : ((⟨d₀, hd₀L⟩ : L) : lBar L) = wb := hn₀w
  have hψd₀ : ψ ((⟨d₀, hd₀L⟩ : L) : lBar L) = ProjGenLinGroup.mk M := by rw [hd₀bar, hψwb]
  have hd₀1 : d₀ ≠ 1 := by
    intro h1
    have h1' : ((⟨d₀, hd₀L⟩ : L) : lBar L) = 1 := by
      rw [show (⟨d₀, hd₀L⟩ : L) = 1 from Subtype.ext h1, QuotientGroup.mk_one]
    have hmk : ProjGenLinGroup.mk M = 1 := by rw [← hψd₀, h1', map_one]
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmk
    obtain ⟨u, hu⟩ := hmk
    have hDu : D₁ = GeneralLinearGroup.scalar (Fin 3) u := by
      have e1 : D₁ = g⁻¹ * M * g := by rw [hM]; group
      rw [e1, ← hu, ← SL3Lines.scalar_mul_comm, inv_mul_cancel_right]
    have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hDu
    have h11 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 1 1) hDu
    simp only [hD₁, coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_one] at h00 h11
    exact hτ₀1 (by rw [← hτuv, h11, ← h00])
  have hd₀T : Sec4.InducesTypeOn L d₀ 1 := by
    have hzZ : GeneralLinearGroup.scalar (Fin 3) τu ∈ Sec4.zPi true 3 (2 ^ f) K := by
      rw [Sec4.zPi_eq (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hτ₀ hτ₀1]
      exact ⟨Sec4.mem_glPi_true _ _, ⟨τu, rfl⟩⟩
    have hτu' : (τu : K) ^ 3 = 1 := by rw [hτuv]; exact hτ₀
    have hτu1' : (τu : K) ≠ 1 := by rw [hτuv]; exact hτ₀1
    refine ⟨hAL hn₀A, true, 2, f, K, inferInstance, hPi, hmod, e, M,
      Sec4.mem_glPi_true _ _, ⟨(τu : K), hτu', hτu1', _, hzZ, g, Sec4.mem_glPi_true _ _, ?_⟩, ?_⟩
    · rw [diagTau_eq hτu', hM, ← hD₁]
      calc g⁻¹ * (g * D₁ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) τu) * g
          = g⁻¹ * (g * D₁ * (GeneralLinearGroup.scalar (Fin 3) τu * g⁻¹)) * g := by
            rw [SL3Lines.scalar_mul_comm τu g⁻¹]
            group
        _ = D₁ * GeneralLinearGroup.scalar (Fin 3) τu := by group
        _ = GeneralLinearGroup.scalar (Fin 3) τu * D₁ := (SL3Lines.scalar_mul_comm τu D₁).symm
    · intro z
      rw [thetaQuotMulAut_inner hd₀L, map_mul, map_mul, map_inv, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hψe, hψd₀]
  have hmk_of : ∀ (y Y' : GL (Fin 3) K) (l : Kˣ),
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * Y' →
        ProjGenLinGroup.mk y = ProjGenLinGroup.mk (g * Y' * g⁻¹) := by
    intro y Y' l h
    have hy : y = GeneralLinearGroup.scalar (Fin 3) l * (g * Y' * g⁻¹) := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = g * GeneralLinearGroup.scalar (Fin 3) l * Y' * g⁻¹ := by rw [h]; group
        _ = GeneralLinearGroup.scalar (Fin 3) l * (g * Y' * g⁻¹) := by
            rw [← SL3Lines.scalar_mul_comm l g]
            group
    rw [hy, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  have hD₁inv : D₁⁻¹ = diagUnits 1 (τu ^ 2) τu := by
    rw [hD₁, inv_eq_iff_mul_eq_one, Sec4.diagUnits_mul, mul_one, ← pow_succ, hτu3,
      ← pow_succ', hτu3, SL3Lines.diagUnits_one_one_one]
  have hTU' : ∀ (b : G) (hb : b ∈ A ⊓ L), b ≠ 1 →
      (∃ m : lBar L, m * ((⟨b, hb.2⟩ : L) : lBar L) * m⁻¹ = ((⟨b, hb.2⟩ : L) : lBar L)⁻¹) →
        b = d₀ ∨ b = d₀⁻¹ := by
    intro b hb hb1 ⟨m, hm⟩
    obtain ⟨y, hyD, hy⟩ := hyA b hb.1
    set B' : lBar L := ((⟨b, hb.2⟩ : L) : lBar L) with hB'
    have hψb : ψ B' = ProjGenLinGroup.mk y := by
      refine coe_e_eq_mk_of_inner hPi hmod hq2 e B' y fun z => ?_
      have h1 := hy z
      rw [show T ⟨b, hAL hb.1⟩ z = B' * z * B'⁻¹ from hTinner b hb.2 z] at h1
      exact h1
    obtain ⟨l, s, t, hs, ht, hyg⟩ := hdiag y hyD
    obtain ⟨r, -, hrm⟩ := (e m).2
    have hψm : ψ m = ProjGenLinGroup.mk r := by rw [hψe]; exact hrm.symm
    have h1 : ProjGenLinGroup.mk (r * y * r⁻¹) = ProjGenLinGroup.mk y⁻¹ := by
      have h0 := congrArg ψ hm
      rw [map_mul, map_mul, map_inv, map_inv, hψb, hψm] at h0
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h0
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
    have h3 : (g⁻¹ * r * g) * (g⁻¹ * y * g) * (g⁻¹ * r * g)⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) u = (g⁻¹ * y * g)⁻¹ := by
      calc (g⁻¹ * r * g) * (g⁻¹ * y * g) * (g⁻¹ * r * g)⁻¹ *
            GeneralLinearGroup.scalar (Fin 3) u
          = g⁻¹ * (r * y * r⁻¹) * (g * GeneralLinearGroup.scalar (Fin 3) u) := by group
        _ = g⁻¹ * (r * y * r⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
            rw [← SL3Lines.scalar_mul_comm u g]
            group
        _ = (g⁻¹ * y * g)⁻¹ := by rw [hu]; group
    rw [hyg] at h3
    have hs3 : (s : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 s).mp hs, Units.val_one]
    have ht3 : (t : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 t).mp ht, Units.val_one]
    rcases eq_of_conj_inv h2 hτ₀ hτ₀1 hs3 ht3 h3 with ⟨hs1, ht1⟩ | ⟨hsτ, htτ⟩ | ⟨hsτ, htτ⟩
    ·
      exfalso
      have hs1' : s = 1 := Units.ext hs1
      have ht1' : t = 1 := Units.ext ht1
      rw [hs1', ht1', SL3Lines.diagUnits_one_one_one] at hyg
      have hmy := hmk_of y 1 l (by rw [hyg, mul_one])
      rw [mul_one, mul_inv_cancel, map_one] at hmy
      have hB1 : B' = ((⟨1, L.one_mem⟩ : L) : lBar L) := by
        apply hψinj
        rw [hψb, hmy, show (⟨1, L.one_mem⟩ : L) = 1 from rfl, QuotientGroup.mk_one, map_one]
      exact hb1 (hinjAL b 1 hb (one_mem _) hB1)
    ·
      left
      have hs' : s = τu := Units.ext (by rw [hsτ, hτuv])
      have ht' : t = τu ^ 2 := Units.ext (by rw [htτ, Units.val_pow_eq_pow_val, hτuv])
      rw [hs', ht'] at hyg
      have hmy := hmk_of y D₁ l hyg
      apply hinjAL b d₀ hb hd₀B
      apply hψinj
      rw [hψb, hψd₀, hmy]
    ·
      right
      have hs' : s = τu ^ 2 := Units.ext (by rw [hsτ, Units.val_pow_eq_pow_val, hτuv])
      have ht' : t = τu := Units.ext (by rw [htτ, hτuv])
      rw [hs', ht', ← hD₁inv] at hyg
      have hmy := hmk_of y D₁⁻¹ l hyg
      have hd₀iB : d₀⁻¹ ∈ A ⊓ L := (A ⊓ L).inv_mem hd₀B
      apply hinjAL b d₀⁻¹ hb hd₀iB
      apply hψinj
      have e1 : ((⟨d₀⁻¹, hd₀iB.2⟩ : L) : lBar L) = ((⟨d₀, hd₀L⟩ : L) : lBar L)⁻¹ := by
        rw [← QuotientGroup.mk_inv]
        rfl
      rw [hψb, e1, map_inv, hψd₀, hmy, ← map_inv, hM]
      congr 1
      group
  obtain ⟨m₀, hm₀⟩ := exists_conj_inv_of_inducesTypeOn_one hn eL hd₀L hd₀T
  have hAUT : ∀ x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (A : Set G),
      x * d₀ * x⁻¹ = d₀ ∨ x * d₀ * x⁻¹ = d₀⁻¹ := by
    rintro x ⟨hxL, hxA⟩
    have hbA : x * d₀ * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxA d₀).mp hn₀A
    have hbL : x * d₀ * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL d₀).mp hd₀L
    have hb1 : x * d₀ * x⁻¹ ≠ 1 := by
      intro h
      apply hd₀1
      calc d₀ = x⁻¹ * (x * d₀ * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxL⟩) with hσ
    have hσd : σ ((⟨d₀, hd₀L⟩ : L) : lBar L) = ((⟨x * d₀ * x⁻¹, hbL⟩ : L) : lBar L) := by
      rw [hσ, Sec4.thetaQuotMulAut_mk]
      rfl
    refine hTU' _ ⟨hbA, hbL⟩ hb1 ⟨σ m₀, ?_⟩
    rw [← hσd, ← map_mul, ← map_inv, ← map_mul, hm₀, map_inv]
  have hDIAG : ∀ (x : G) (hxL : x ∈ L), x ∈ Subgroup.normalizer (A : Set G) →
      ∀ sx : GL (Fin 3) K, ψ ((⟨x, hxL⟩ : L) : lBar L) = ProjGenLinGroup.mk sx →
        sx * M = M * sx → ∀ a ∈ A, a * x = x * a := by
    intro x hxL hxA sx hsx hxM a ha
    have hND : (g⁻¹ * sx * g) * D₁ = D₁ * (g⁻¹ * sx * g) := by
      have e1 : (g⁻¹ * sx * g) * D₁ = g⁻¹ * (sx * M) * g := by rw [hM]; group
      have e2 : D₁ * (g⁻¹ * sx * g) = g⁻¹ * (M * sx) * g := by rw [hM]; group
      rw [e1, e2, hxM]
    have hD₁m : ((D₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, τ₀, τ₀ ^ 2] := by
      rw [hD₁, coe_diagUnits]
      simp [Units.val_pow_eq_pow_val, hτuv]
    have hNmat : ((g⁻¹ * sx * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![1, τ₀, τ₀ ^ 2] =
        diagonal ![1, τ₀, τ₀ ^ 2] * ((g⁻¹ * sx * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hD₁m, ← Units.val_mul, ← Units.val_mul, hND]
    obtain ⟨y, hyD, hy⟩ := hyA a ha
    obtain ⟨l, s, t, -, -, hyg⟩ := hdiag y hyD
    have hNY : (g⁻¹ * sx * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * sx * g) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hyg, Sec4.scalar_mul_diagUnits_eq, Sec4.coe_diagHom]
      exact commute_diagonal_of_commute hτ₀ hτ₀1 hNmat _
    have hsy : sx * y = y * sx := by
      have e1 : sx * y = g * ((g⁻¹ * sx * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      have e2 : y * sx = g * ((g⁻¹ * y * g) * (g⁻¹ * sx * g)) * g⁻¹ := by group
      rw [e1, e2, hNY]
    have hfixx : T ⟨a, hAL ha⟩ ((⟨x, hxL⟩ : L) : lBar L) = ((⟨x, hxL⟩ : L) : lBar L) := by
      apply hψinj
      rw [hy, hsx, ← map_inv, ← map_mul, ← map_mul, ← hsy, mul_inv_cancel_right]
    have hTmk : T ⟨a, hAL ha⟩ ((⟨x, hxL⟩ : L) : lBar L) =
        ((⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL ha) x).mp hxL⟩ : L) : lBar L) :=
      rfl
    rw [hTmk] at hfixx
    have hθ := QuotientGroup.eq.mp hfixx
    have hmem : (a * x * a⁻¹)⁻¹ * x ∈ A := by
      have e : (a * x * a⁻¹)⁻¹ * x = a * (x⁻¹ * a⁻¹ * x) := by group
      rw [e]
      refine A.mul_mem ha ?_
      have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxA) a⁻¹).mp (A.inv_mem ha)
      simpa using h'
    have hu3 : ((⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL ha) x).mp hxL⟩ : L)⁻¹ *
        ⟨x, hxL⟩) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      simpa using h3 _ hmem
    have hu1 := hθ3 _ hθ 1 hu3
    have hu1' : (a * x * a⁻¹)⁻¹ * x = 1 := by simpa using congrArg Subtype.val hu1
    have hax : a * x * a⁻¹ = x := inv_mul_eq_one.mp hu1'
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [hax]
  have hLAMBDA : ∀ (x : G) (hxL : x ∈ L), x ∈ Subgroup.normalizer (A : Set G) →
      x * d₀ * x⁻¹ = d₀ → ∀ a ∈ A, a * x ^ 3 = x ^ 3 * a := by
    intro x hxL hxA hxd
    obtain ⟨sx, -, hsx⟩ := (e ((⟨x, hxL⟩ : L) : lBar L)).2
    have hψx : ψ ((⟨x, hxL⟩ : L) : lBar L) = ProjGenLinGroup.mk sx := by
      rw [hψe]
      exact hsx.symm
    have hcx : ((⟨x, hxL⟩ : L) : lBar L) * ((⟨d₀, hd₀L⟩ : L) : lBar L) *
        ((⟨x, hxL⟩ : L) : lBar L)⁻¹ = ((⟨d₀, hd₀L⟩ : L) : lBar L) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hxd
    have h1 : ProjGenLinGroup.mk (sx * M * sx⁻¹) = ProjGenLinGroup.mk M := by
      have h0 := congrArg ψ hcx
      rw [map_mul, map_mul, map_inv, hψx, hψd₀] at h0
      rw [map_mul, map_mul, map_inv]
      exact h0
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
    have hu3 : u ^ 3 = 1 := by
      have h2 : (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) ^ 3 = 1 := by
        rw [hu, hM3]
      have e1 : (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) ^ 3 =
          sx * M ^ 3 * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) (u ^ 3) := by
        have hc : ∀ X : GL (Fin 3) K, X * GeneralLinearGroup.scalar (Fin 3) u =
            GeneralLinearGroup.scalar (Fin 3) u * X := fun X => (SL3Lines.scalar_mul_comm u X).symm
        rw [map_pow, pow_three, pow_three, pow_three]
        calc sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
              (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
                (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u))
            = sx * M * sx⁻¹ * (GeneralLinearGroup.scalar (Fin 3) u * (sx * M * sx⁻¹)) *
                (GeneralLinearGroup.scalar (Fin 3) u * (sx * M * sx⁻¹)) *
                GeneralLinearGroup.scalar (Fin 3) u := by group
          _ = sx * M * sx⁻¹ * (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) *
                (sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) *
                GeneralLinearGroup.scalar (Fin 3) u := by rw [← hc]
          _ = sx * M * sx⁻¹ * (sx * M * sx⁻¹) * (GeneralLinearGroup.scalar (Fin 3) u *
                (sx * M * sx⁻¹)) * GeneralLinearGroup.scalar (Fin 3) u *
                GeneralLinearGroup.scalar (Fin 3) u := by group
          _ = sx * M * sx⁻¹ * (sx * M * sx⁻¹) * (sx * M * sx⁻¹ *
                GeneralLinearGroup.scalar (Fin 3) u) * GeneralLinearGroup.scalar (Fin 3) u *
                GeneralLinearGroup.scalar (Fin 3) u := by rw [← hc]
          _ = sx * (M * (M * M)) * sx⁻¹ * (GeneralLinearGroup.scalar (Fin 3) u *
                (GeneralLinearGroup.scalar (Fin 3) u * GeneralLinearGroup.scalar (Fin 3) u)) := by
              group
      rw [e1, hM3, mul_one, mul_inv_cancel, one_mul] at h2
      have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp only [scalar_apply_self', Units.val_one, Matrix.one_apply_eq] at h00
      exact Units.ext (by rw [h00, Units.val_one])
    have hc1 : sx * M * sx⁻¹ = M * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
      calc sx * M * sx⁻¹ = sx * M * sx⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
            (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
        _ = M * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by rw [hu, map_inv]
    have hu3' : u⁻¹ * (u⁻¹ * u⁻¹) = 1 := by
      rw [← pow_two, ← pow_succ', inv_pow, hu3, inv_one]
    have hM3' : sx ^ 3 * M * (sx ^ 3)⁻¹ = M := by
      calc sx ^ 3 * M * (sx ^ 3)⁻¹ = sx * (sx * (sx * M * sx⁻¹) * sx⁻¹) * sx⁻¹ := by
            rw [pow_three]
            group
        _ = sx * (sx * (M * GeneralLinearGroup.scalar (Fin 3) u⁻¹) * sx⁻¹) * sx⁻¹ := by
            rw [hc1]
        _ = sx * ((sx * M * sx⁻¹) * (sx * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * sx⁻¹)) *
            sx⁻¹ := by group
        _ = sx * (M * GeneralLinearGroup.scalar (Fin 3) u⁻¹ *
            GeneralLinearGroup.scalar (Fin 3) u⁻¹) * sx⁻¹ := by
            rw [hc1, Item21LateProof.conj_scalar]
        _ = (sx * M * sx⁻¹) * (sx * GeneralLinearGroup.scalar (Fin 3) (u⁻¹ * u⁻¹) * sx⁻¹) := by
            rw [map_mul]
            group
        _ = M * GeneralLinearGroup.scalar (Fin 3) (u⁻¹ * (u⁻¹ * u⁻¹)) := by
            rw [hc1, Item21LateProof.conj_scalar, mul_assoc, ← map_mul]
        _ = M := by rw [hu3', map_one, mul_one]
    have hcomm3 : sx ^ 3 * M = M * sx ^ 3 := by
      calc sx ^ 3 * M = sx ^ 3 * M * (sx ^ 3)⁻¹ * sx ^ 3 := by group
        _ = M * sx ^ 3 := by rw [hM3']
    have hx3L : x ^ 3 ∈ L := L.pow_mem hxL 3
    have hψx3 : ψ ((⟨x ^ 3, hx3L⟩ : L) : lBar L) = ProjGenLinGroup.mk (sx ^ 3) := by
      have e1 : (⟨x ^ 3, hx3L⟩ : L) = (⟨x, hxL⟩ : L) ^ 3 := Subtype.ext (by simp)
      rw [e1, QuotientGroup.mk_pow, map_pow, hψx, map_pow]
    exact hDIAG (x ^ 3) hx3L (Subgroup.pow_mem _ hxA 3) (sx ^ 3) hψx3 hcomm3
  have hmk_conj_eq : ∀ N N' : GL (Fin 3) K, (∀ z, ProjGenLinGroup.mk N * ψ z *
      (ProjGenLinGroup.mk N)⁻¹ = ProjGenLinGroup.mk N' * ψ z * (ProjGenLinGroup.mk N')⁻¹) →
        ProjGenLinGroup.mk N = ProjGenLinGroup.mk N' := by
    intro N N' h
    refine mk_eq_of_conj_eq hPi hmod hq2 fun s hs => ?_
    have h1 := h (e.symm ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩)
    rwa [hψe, MulEquiv.apply_symm_apply] at h1
  set m₃ : GL (Fin 3) K := g * Sec4.cycThree * g⁻¹ with hm₃
  have hm₃SL : m₃ ∈ Sec4.slPi true 3 (2 ^ f) K := by
    rw [Sec4.mem_slPi_true, hm₃, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      det_cycThree, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]
  set wb₃ : lBar L := e.symm ⟨ProjGenLinGroup.mk m₃, Subgroup.mem_map_of_mem _ hm₃SL⟩ with hwb₃
  have hψwb₃ : ψ wb₃ = ProjGenLinGroup.mk m₃ := by rw [hψe, hwb₃, MulEquiv.apply_symm_apply]
  have hwb₃3 : wb₃ ^ 3 = 1 := by
    apply hψinj
    rw [map_pow, hψwb₃, ← map_pow, hm₃, conj_pow, cycThree_pow_three, mul_one, mul_inv_cancel,
      map_one, map_one]
  obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective wb₃
  have hw₀L : (w₀ : G) ∈ L := w₀.2
  have hTw₀ : ∀ z, ψ (T ⟨(w₀ : G), Subgroup.le_normalizer hw₀L⟩ z) =
      ProjGenLinGroup.mk m₃ * ψ z * (ProjGenLinGroup.mk m₃)⁻¹ := by
    intro z
    rw [hTinner _ hw₀L z, map_mul, map_mul, map_inv, show ((⟨(w₀ : G), hw₀L⟩ : L) : lBar L) =
      wb₃ from hw₀, hψwb₃]
  have hTw₀i : ∀ z, ψ (T ⟨(w₀ : G)⁻¹, Subgroup.le_normalizer (L.inv_mem hw₀L)⟩ z) =
      (ProjGenLinGroup.mk m₃)⁻¹ * ψ z * ProjGenLinGroup.mk m₃ := by
    intro z
    rw [hTinner _ (L.inv_mem hw₀L) z, map_mul, map_mul, map_inv]
    have e1 : ((⟨(w₀ : G)⁻¹, L.inv_mem hw₀L⟩ : L) : lBar L) = wb₃⁻¹ := by
      rw [← hw₀, ← QuotientGroup.mk_inv]
      rfl
    rw [e1, map_inv, hψwb₃, inv_inv]
  have hw₀N : ∀ x ∈ A,
      (w₀ : G) * x * (w₀ : G)⁻¹ ∈ A ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := hyA x hx
    obtain ⟨l, s, t, hs, ht, hyg⟩ := hdiag y hyD
    obtain ⟨y', hy'D, l', hy'g⟩ := hsurj _ (inv_mem ht) _ (mul_mem hs (inv_mem ht))
    obtain ⟨τ', hτ', hτ'y⟩ := hconj' y' hy'D
    obtain ⟨x', hx'N, hx'A, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ'
    have hm₃y : ProjGenLinGroup.mk (m₃ * y * m₃⁻¹) = ProjGenLinGroup.mk y' := by
      rw [hmk_of y' _ l' hy'g]
      refine hmk_of _ _ (l * t) ?_
      rw [show g⁻¹ * (m₃ * y * m₃⁻¹) * g = Sec4.cycThree * (g⁻¹ * y * g) * Sec4.cycThree⁻¹ by
        rw [hm₃]; group, hyg, cycThree_conj]
    have hconjx : T ⟨(w₀ : G), Subgroup.le_normalizer hw₀L⟩ * T ⟨x, hAL hx⟩ *
        T ⟨(w₀ : G)⁻¹, Subgroup.le_normalizer (L.inv_mem hw₀L)⟩ = T ⟨x', hAL hx'A⟩ := by
      ext z
      apply hψinj
      simp only [MulAut.mul_apply]
      rw [hTw₀, hy, hTw₀i]
      have h1 := hτ'y z
      rw [show (Sec4.thetaQuotMulAut L) (L.normalizerMonoidHom ⟨x', hx'N⟩) z =
        T ⟨x', hAL hx'A⟩ z from rfl] at h1
      rw [← hψe, ← hψe] at h1
      rw [h1, ← hm₃y, map_mul ProjGenLinGroup.mk (m₃ * y) m₃⁻¹,
        map_mul ProjGenLinGroup.mk m₃ y, map_inv ProjGenLinGroup.mk m₃]
      group
    have hxw₀ : x * (w₀ : G)⁻¹ * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL hx) _).mp (L.inv_mem hw₀L)
    have hlwL : (w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹ ∈ L := by
      rw [show (w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹ = (w₀ : G) * (x * (w₀ : G)⁻¹ * x⁻¹) by group]
      exact L.mul_mem hw₀L hxw₀
    have haA : x' * x⁻¹ ∈ A := A.mul_mem hx'A (A.inv_mem hx)
    have hTl : T ⟨x' * x⁻¹, hAL haA⟩ =
        T ⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, Subgroup.le_normalizer hlwL⟩ := by
      have e1 : (⟨x' * x⁻¹, hAL haA⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨x', hAL hx'A⟩ * (⟨x, hAL hx⟩)⁻¹ := rfl
      have e2 : (⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, Subgroup.le_normalizer hlwL⟩ :
          Subgroup.normalizer (L : Set G)) = ⟨(w₀ : G), Subgroup.le_normalizer hw₀L⟩ *
            ⟨x, hAL hx⟩ * ⟨(w₀ : G)⁻¹, Subgroup.le_normalizer (L.inv_mem hw₀L)⟩ *
              (⟨x, hAL hx⟩)⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_mul, map_mul, map_inv, hconjx]
    obtain ⟨n, hnA, hnl, -⟩ := Sec13.Item138Proof.exists_eq_zpow_mul_of_inner hAL hAe hmax hZ hsc
      haA (w := ((⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, hlwL⟩ : L) : lBar L)) (fun z => by
        rw [show (Sec4.thetaQuotMulAut L) (L.normalizerMonoidHom ⟨x' * x⁻¹, hAL haA⟩) z =
          T ⟨x' * x⁻¹, hAL haA⟩ z from rfl, hTl]
        exact hTinner _ hlwL z)
    have hθ : (⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, hlwL⟩ : L) * n⁻¹ ∈
        aschbacherSolvableCore 3 L := by
      have h1 := QuotientGroup.eq_iff_div_mem.mp hnl.symm
      rwa [div_eq_mul_inv] at h1
    have e3 : (w₀ : G) * x * (w₀ : G)⁻¹ =
        (((⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, hlwL⟩ : L) * n⁻¹ : L) : G) * ((n : G) * x) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e3]
    have hθG : (((⟨(w₀ : G) * x * (w₀ : G)⁻¹ * x⁻¹, hlwL⟩ : L) * n⁻¹ : L) : G) ∈
        inSubgroup (aschbacherSolvableCore 3) L := ⟨_, hθ, rfl⟩
    have h4 := Subgroup.mul_mem_sup hθG (A.mul_mem hnA hx)
    rwa [sup_comm] at h4
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  obtain ⟨m, hmL, hmN, hmw⟩ :=
    Sec13.Item138Proof.exists_mem_normalizer_of_conj_mem hAL hA3 hw₀L hw₀N
  have hmbar : ((⟨m, hmL⟩ : L) : lBar L) = wb₃ := by
    rw [← hw₀, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    obtain ⟨t₀, ht₀, ht₀e⟩ := hmw
    have e1 : (⟨m, hmL⟩ : L) * w₀⁻¹ = t₀ := Subtype.ext (by simpa using ht₀e.symm)
    rw [e1]
    exact ht₀
  obtain ⟨k, m', hm', hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 3 (by norm_num)
  set w : G := m ^ (m' * m') with hwdef
  have hwL' : w ∈ L := L.pow_mem hmL _
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hmN _
  have hw3k : w ^ 3 ^ k = 1 := by
    rw [hwdef, ← pow_mul, show m' * m' * 3 ^ k = (3 ^ k * m') * m' by ring, pow_mul, ← hord,
      pow_orderOf_eq_one, one_pow]
  have hm'3 : m' * m' % 3 = 1 := by
    have : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hwbar : ((⟨w, hwL'⟩ : L) : lBar L) = wb₃ := by
    have e1 : (⟨w, hwL'⟩ : L) = (⟨m, hmL⟩ : L) ^ (m' * m') := Subtype.ext (by simp [hwdef])
    rw [e1, QuotientGroup.mk_pow, hmbar, Item21LateProof.pow_eq_pow_mod_three hwb₃3, hm'3,
      pow_one]
  have hw31 : w ^ 3 = 1 := by
    have hmem : (⟨w, hwL'⟩ : L) ^ 3 ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hwbar, hwb₃3]
    have h1 := hθ3 _ hmem k (Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, hw3k, one_pow]))
    simpa using congrArg Subtype.val h1
  have hTw : ∀ z, ψ (T ⟨w, Subgroup.le_normalizer hwL'⟩ z) =
      ProjGenLinGroup.mk m₃ * ψ z * (ProjGenLinGroup.mk m₃)⁻¹ := by
    intro z
    rw [hTinner _ hwL' z, map_mul, map_mul, map_inv, hwbar, hψwb₃]
  have hτu : τu ∈ rootsOfUnity 3 K := (mem_rootsOfUnity _ _).mpr hτu3
  have hwnot : ¬ ∀ a ∈ A, w * a * w⁻¹ = a := by
    intro h
    obtain ⟨y₁, hy₁D, l₁, hy₁g⟩ := hsurj 1 (one_mem _) τu hτu
    obtain ⟨τ₁, hτ₁, hτ₁y⟩ := hconj' y₁ hy₁D
    obtain ⟨a₁, ha₁N, ha₁A, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ₁
    have hTa₁ : ∀ z, ψ (T ⟨a₁, hAL ha₁A⟩ z) =
        ProjGenLinGroup.mk y₁ * ψ z * (ProjGenLinGroup.mk y₁)⁻¹ := fun z => hτ₁y z
    have hwa : w * a₁ * w⁻¹ = a₁ := h a₁ ha₁A
    have hT1 : T ⟨w, Subgroup.le_normalizer hwL'⟩ * T ⟨a₁, hAL ha₁A⟩ *
        T ⟨w⁻¹, Subgroup.le_normalizer (L.inv_mem hwL')⟩ = T ⟨a₁, hAL ha₁A⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hwa)
    have hTwi : ∀ z, ψ (T ⟨w⁻¹, Subgroup.le_normalizer (L.inv_mem hwL')⟩ z) =
        (ProjGenLinGroup.mk m₃)⁻¹ * ψ z * ProjGenLinGroup.mk m₃ := by
      intro z
      rw [hTinner _ (L.inv_mem hwL') z, map_mul, map_mul, map_inv]
      have e1 : ((⟨w⁻¹, L.inv_mem hwL'⟩ : L) : lBar L) = wb₃⁻¹ := by
        rw [← hwbar, ← QuotientGroup.mk_inv]
        rfl
      rw [e1, map_inv, hψwb₃, inv_inv]
    have hmk1 : ProjGenLinGroup.mk (m₃ * y₁ * m₃⁻¹) = ProjGenLinGroup.mk y₁ := by
      refine hmk_conj_eq _ _ fun z => ?_
      have h2 := congrArg (fun φ : MulAut (lBar L) => ψ (φ z)) hT1
      simp only [MulAut.mul_apply, hTw, hTa₁, hTwi] at h2
      rw [map_mul ProjGenLinGroup.mk (m₃ * y₁) m₃⁻¹, map_mul ProjGenLinGroup.mk m₃ y₁,
        map_inv ProjGenLinGroup.mk m₃, ← h2]
      group
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk1
    have hconjg : Sec4.cycThree * (g⁻¹ * y₁ * g) * Sec4.cycThree⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) u = g⁻¹ * y₁ * g := by
      calc Sec4.cycThree * (g⁻¹ * y₁ * g) * Sec4.cycThree⁻¹ * GeneralLinearGroup.scalar (Fin 3) u
          = g⁻¹ * (m₃ * y₁ * m₃⁻¹) * (g * GeneralLinearGroup.scalar (Fin 3) u) := by
            rw [hm₃]
            group
        _ = g⁻¹ * (m₃ * y₁ * m₃⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
            rw [← SL3Lines.scalar_mul_comm u g]
            group
        _ = g⁻¹ * y₁ * g := by rw [hu]
    rw [hy₁g, cycThree_conj] at hconjg
    have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hconjg
    have h11 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 1 1) hconjg
    simp [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits,
      Matrix.diagonal_mul_diagonal] at h00 h11
    rw [h11, Units.val_one, mul_one] at h00
    have hl0 : (l₁ : K) ≠ 0 := l₁.ne_zero
    have h1 : (τu : K) = 1 := by
      calc (τu : K) = (l₁ : K)⁻¹ * ((l₁ : K) * τu) := by field_simp
        _ = 1 := by rw [h00, inv_mul_cancel₀ hl0]
    exact hτ₀1 (by rw [← hτuv]; exact h1)
  have hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a := fun a _ => by
    rw [hw31, one_mul, inv_one, mul_one]
  have hwA : ∀ a ∈ A, w * a * w⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hwN a).mp ha
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL'), mul_inv_cancel_right]
  have hd₀3 : d₀ ^ 3 = 1 := h3 d₀ hn₀A
  have hwd : w * d₀ * w⁻¹ = d₀ := by
    rcases hAUT w ⟨Subgroup.le_normalizer hwL', hwN⟩ with h | h
    · exact h
    · exfalso
      have e1 : w ^ 3 * d₀ * (w ^ 3)⁻¹ = d₀⁻¹ := by
        calc w ^ 3 * d₀ * (w ^ 3)⁻¹ = w * (w * (w * d₀ * w⁻¹) * w⁻¹) * w⁻¹ := by
              rw [pow_three]
              group
          _ = w * (w * d₀⁻¹ * w⁻¹) * w⁻¹ := by rw [h]
          _ = w * (w * d₀ * w⁻¹)⁻¹ * w⁻¹ := by group
          _ = d₀⁻¹ := by rw [h, inv_inv, h]
      rw [hw3 d₀ hn₀A] at e1
      apply hd₀1
      have h2' : d₀ * d₀ = 1 := mul_eq_one_iff_eq_inv.mpr e1
      calc d₀ = d₀ ^ 3 * (d₀ * d₀)⁻¹ := by rw [pow_three]; group
        _ = 1 := by rw [hd₀3, h2']; group
  have hd₀c : d₀ ∉ Subgroup.zpowers c := by
    intro h
    apply hcL
    have hZ' : Subgroup.zpowers d₀ = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime hd₀3 hd₀1])
    have hcd : c ∈ Subgroup.zpowers d₀ := hZ' ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hd₀L) hcd
  have hB₀9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA d₀ hn₀A) (h3 c hcA) hd₀3
    hc1 hd₀c
  have hB₀A : Subgroup.zpowers c ⊔ Subgroup.zpowers d₀ ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hn₀A)
  have hcd' : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d₀, x * y = y * x :=
    fun x hx y hy => hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) y
      ((Subgroup.zpowers_le.mpr hn₀A) hy)
  have hB₀set := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcd').2
  have hwfixB : ∀ y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d₀, w * y * w⁻¹ = y := by
    intro y hy
    have hy' : y ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d₀ : Subgroup G) : Set G) := hy
    rw [hB₀set] at hy'
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hy'
    rw [show w * (x₁ * y₁) * w⁻¹ = (w * x₁ * w⁻¹) * (w * y₁ * w⁻¹) by group,
      Item21LateProof.conj_eq_of_mem_zpowers hwc hx₁,
      Item21LateProof.conj_eq_of_mem_zpowers hwd hy₁]
  have hcomm_w := Item21LateProof.inv_mul_conj_mem_of_pow_three hcomm h3 hB₀A
    (by rw [h27, hB₀9]; norm_num) hwA (fun y hy => by rw [hwfixB y hy]; exact hy) hw3
  have hwAL : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ L := by
    intro a ha
    have h1 : a⁻¹ * w * a⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL (A.inv_mem ha)) w).mp hwL'
    have e : a⁻¹ * (w * a * w⁻¹) = a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ := by group
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hwL')
  have hB₀L : ∀ y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d₀, y ∈ L →
      y ∈ Subgroup.zpowers d₀ := by
    intro y hy hyL
    have hy' : y ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d₀ : Subgroup G) : Set G) := hy
    rw [hB₀set] at hy'
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hy'
    have hx₁L : x₁ ∈ L := by
      have := L.mul_mem hyL (L.inv_mem ((Subgroup.zpowers_le.mpr hd₀L) hy₁))
      rwa [mul_inv_cancel_right] at this
    have hx₁1 : x₁ = 1 := by
      by_contra hne
      apply hcL
      have hx₁3 : x₁ ^ 3 = 1 := h3 x₁ ((Subgroup.zpowers_le.mpr hcA) hx₁)
      have hZ' : Subgroup.zpowers x₁ = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₁)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime hx₁3 hne])
      have hcx : c ∈ Subgroup.zpowers x₁ := hZ' ▸ Subgroup.mem_zpowers c
      exact (Subgroup.zpowers_le.mpr hx₁L) hcx
    rw [hx₁1]
    simpa using hy₁
  have hwAd : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers d₀ :=
    fun a ha => hB₀L _ (hcomm_w a ha) (hwAL a ha)
  have hwmove : ∃ a ∈ A, w * a * w⁻¹ ≠ a := by
    by_contra h
    push Not at h
    exact hwnot h
  set σ₁ : starOf A L := eS.symm (Equiv.swap 0 1) with hσ₁
  have hσ₁2 : orderOf σ₁ = 2 := by
    rw [hσ₁, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  obtain ⟨⟨t, htN⟩, htL, htσ⟩ := σ₁.2
  have htL' : t ∈ L := Subgroup.mem_subgroupOf.mp htL
  have hφ2 : orderOf (A.normalizerMonoidHom ⟨t, htN⟩) = 2 := by
    rw [htσ, Subgroup.orderOf_coe, hσ₁2]
  have htd : t * d₀ * t⁻¹ = d₀⁻¹ := by
    rcases hAUT t ⟨Subgroup.le_normalizer htL', htN⟩ with h | h
    · exfalso
      have hcen := hLAMBDA t htL' htN h
      have h1 : A.normalizerMonoidHom ⟨t, htN⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have e : (⟨t, htN⟩ : Subgroup.normalizer (A : Set G)) ^ 3 =
            ⟨t ^ 3, Subgroup.pow_mem _ htN 3⟩ := Subtype.ext (by simp)
        rw [e]
        apply MulEquiv.ext
        intro a
        apply Subtype.ext
        rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply, ← hcen a a.2,
          mul_inv_cancel_right]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hφ2] at h2
      norm_num at h2
    · exact h
  have hHW := Sec13.normalizer_inf_le_of_mem hLc hAL hsc hn₀A hd₀L hd₀c
  refine ⟨hcL, d₀, hd₀B, hd₀1, hd₀T,
    fun d hd hd1 hdT => hTU' d hd hd1 (exists_conj_inv_of_inducesTypeOn_one hn eL hd.2 hdT),
    hAUT, fun x hx => hAUT x ⟨hHW hx, hx.2⟩, hHW, ⟨w, ⟨hwL', hwN⟩, hw31, hwd, hwAd, hwmove⟩, t,
    ⟨htL', htN⟩, htd⟩

end Frame

end CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof

namespace CFSG.RankThree.PartTwo.Sec21

theorem item2119Frame_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2119Frame := by
  intro G _ _ A E U c L hcfg
  obtain ⟨-, d₀, hd₀B, hd₀1, hd₀T, -, -, -, -, ⟨w, hw, -, hw'⟩, ht⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  exact ⟨d₀, hd₀B, hd₀1, hd₀T, ⟨w, hw, hw'⟩, ht⟩

end CFSG.RankThree.PartTwo.Sec21
