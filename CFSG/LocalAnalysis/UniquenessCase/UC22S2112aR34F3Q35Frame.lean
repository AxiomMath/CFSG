module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearGeometry
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
import TauCeti.LinearAlgebra.Matrix.Diagonal
import CFSG.LieType.HighestRoot.CentTrialitySL2
import CFSG.GH74.Generic.BProg.B2.GenLocU3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin412
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Core
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.ClassicalInvolution.Q3.Q3T6FaField
import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
import CFSG.GH74.GLS.C3.Layer2.FusionTools
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.SolvAut
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
import CFSG.GH74.Generic.BProg.B1.Assembly2
import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
import CFSG.GH74.Generic.BProg.B2.GenLocL3Lin
import CFSG.GH74.Generic.BProg.B2.GenLocL3Pair
import CFSG.GH74.Generic.BProg.Stage2Frozen
import CFSG.GH74.Generic.BProg.Theta32
import CFSG.GH74.Generic.Gen4LiftJ
import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.LargeExtraspecial.Types
import CFSG.LieType.HighestRoot.CentTrialityMain
import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25
import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Solomon
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RRes
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)

private theorem isDiag_of_forall_commute_single {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {M : Matrix ι ι F} (hM : ∀ j, ∃ b, Commute (Matrix.single j b (1 : F)) M) :
    M.IsDiag := by
  intro i j hij
  obtain ⟨b, hb⟩ := hM j
  exact Matrix.col_eq_zero_of_commute_single hb hij

private theorem eq_one_of_isDiag_of_pow_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] {M : Matrix ι ι F} (hM : M.IsDiag)
    (h : M ^ p = 1) : M = 1 := by
  rw [← hM.diagonal_diag, Matrix.diagonal_pow, ← Matrix.diagonal_one,
    Matrix.diagonal_eq_diagonal_iff] at h
  rw [← hM.diagonal_diag, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  intro i
  apply frobenius_inj F p
  simpa [frobenius_def] using h i

private theorem pow_card_sub_one_eq_one_of_isDiag {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] {M : Matrix ι ι F} (hM : M.IsDiag) (hdet : M.det ≠ 0) :
    M ^ (Fintype.card F - 1) = 1 := by
  have hne : ∀ i, M.diag i ≠ 0 := by
    intro i hi
    apply hdet
    rw [← hM.diagonal_diag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [← hM.diagonal_diag, Matrix.diagonal_pow, ← Matrix.diagonal_one,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  exact FiniteField.pow_card_sub_one_eq_one _ (hne i)

private theorem commutator_pow_eq_one_of_commute {G : Type} [Group G] {g u : G} {p : ℕ}
    (hz : Commute (g * u * g⁻¹ * u⁻¹) u) (hu : u ^ p = 1) : (g * u * g⁻¹ * u⁻¹) ^ p = 1 := by
  have h1 : g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
  have h2 : (g * u * g⁻¹) ^ p = 1 := by rw [conj_pow, hu, mul_one, mul_inv_cancel]
  rwa [h1, hz.mul_pow, hu, mul_one] at h2

private theorem eq_bot_of_isPGroup_of_forall_pow_eq_one {G : Type} [Group G] {r N : ℕ}
    {B : Subgroup G} (hB : IsPGroup r B) (hcop : Nat.Coprime r N) (hpow : ∀ x ∈ B, x ^ N = 1) :
    B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hB ⟨x, hx⟩
  have h1 : orderOf x ∣ r ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ N := orderOf_dvd_of_pow_eq_one (hpow x hx)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) h1 h2))

section PSLHelpers

private theorem transvection_pow_natCast {n : ℕ} {F : Type} [Field F] {i j : Fin n}
    (hij : i ≠ j) (k : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) ^ k =
      Matrix.SpecialLinearGroup.transvection hij (k : F) := by
  induction k with
  | zero => simp [Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

private theorem transvection_pow_char {n : ℕ} {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] {i j : Fin n} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) ^ p = 1 := by
  rw [transvection_pow_natCast hij p, CharP.cast_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

private theorem commute_single_of_commute_one_add_single
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Ring F]
    {G : Matrix ι ι F} {a b : ι} (c : F)
    (h : Commute (1 + Matrix.single a b c) G) :
    Commute (Matrix.single a b c) G := by
  have h1 : (1 + Matrix.single a b c) * G = G * (1 + Matrix.single a b c) := h
  have h2 : G + Matrix.single a b c * G = G + G * Matrix.single a b c := by
    simpa only [add_mul, mul_add, one_mul, mul_one] using h1
  exact add_left_cancel h2

private theorem commute_single_of_commute_of_coe_eq_one_add_single
    {n : ℕ} {F : Type} [Field F] {g u : Matrix.SpecialLinearGroup (Fin n) F}
    {a b : Fin n} {c : F}
    (hu : (u : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single a b c)
    (h : Commute g u) :
    Commute (Matrix.single a b c) (g : Matrix (Fin n) (Fin n) F) := by
  have hm : ((g * u : Matrix.SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      ((u * g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hu] at hm
  exact commute_single_of_commute_one_add_single c hm.symm

private theorem eq_one_of_mem_center_of_pow_eq_one_sl {N : ℕ} {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hN : 2 ≤ N) {z : Matrix.SpecialLinearGroup (Fin N) F}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) F)) (hzp : z ^ p = 1) :
    z = 1 := by
  apply Subtype.ext
  have hzmatpow : (z : Matrix (Fin N) (Fin N) F) ^ p = 1 := by
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin N) F =>
      (y : Matrix (Fin N) (Fin N) F)) hzp
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using this
  have hdiag : (z : Matrix (Fin N) (Fin N) F).IsDiag := by
    refine isDiag_of_forall_commute_single (fun j => ?_)
    have hb : ∃ b : Fin N, b ≠ j := by
      by_cases h0 : j.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h
        have := congrArg Fin.val h
        simp [h0] at this
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro h
        have := congrArg Fin.val h
        exact h0 (by simpa using this.symm)
    obtain ⟨b, hbj⟩ := hb
    exact ⟨b, commute_single_of_commute_of_coe_eq_one_add_single
      (Matrix.SpecialLinearGroup.transvection_coe hbj.symm (1 : F))
      (Subgroup.mem_center_iff.mp hz
        (Matrix.SpecialLinearGroup.transvection hbj.symm (1 : F))).symm⟩
  exact eq_one_of_isDiag_of_pow_eq_one hdiag hzmatpow

private theorem commute_single_of_commute_map_transvection {N : ℕ} {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] {X : Type} [Group X]
    {ψ : Matrix.SpecialLinearGroup (Fin N) F →* X}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) F))
    {g : Matrix.SpecialLinearGroup (Fin N) F} {a b : Fin N} (hab : a ≠ b)
    (h : Commute (ψ g) (ψ (Matrix.SpecialLinearGroup.transvection hab (1 : F)))) :
    Commute (Matrix.single a b (1 : F)) (g : Matrix (Fin N) (Fin N) F) := by
  set u := Matrix.SpecialLinearGroup.transvection hab (1 : F) with hu
  have hz : g * u * g⁻¹ * u⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) F) := by
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h.eq]
    group
  have hN : 2 ≤ N := by
    have := a.isLt
    have := b.isLt
    have := Fin.val_ne_of_ne hab
    omega
  have hz1 : g * u * g⁻¹ * u⁻¹ = 1 :=
    eq_one_of_mem_center_of_pow_eq_one_sl hN hz
      (commutator_pow_eq_one_of_commute (Subgroup.mem_center_iff.mp hz u).symm
        (transvection_pow_char hab))
  have hgu : Commute g u := by
    show g * u = u * g
    calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
      _ = u * g := by rw [hz1, one_mul]
  exact commute_single_of_commute_of_coe_eq_one_add_single
    (Matrix.SpecialLinearGroup.transvection_coe hab (1 : F)) hgu

private theorem isDiag_of_commute_map_transvection {N : ℕ} {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] {X : Type} [Group X]
    {ψ : Matrix.SpecialLinearGroup (Fin N) F →* X}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) F))
    {g : Matrix.SpecialLinearGroup (Fin N) F}
    (h : ∀ k l : Fin N, k ≠ l → ∃ (a b : Fin N) (hab : a ≠ b), (a = l ∨ b = k) ∧
      Commute (ψ g) (ψ (Matrix.SpecialLinearGroup.transvection hab (1 : F)))) :
    (g : Matrix (Fin N) (Fin N) F).IsDiag := by
  intro k l hkl
  obtain ⟨a, b, hab, hal | hbk, hc⟩ := h k l hkl
  · subst hal
    exact Matrix.col_eq_zero_of_commute_single
      (commute_single_of_commute_map_transvection hker hab hc) hkl
  · subst hbk
    exact Matrix.row_eq_zero_of_commute_single
      (commute_single_of_commute_map_transvection hker hab hc) hkl.symm

private theorem pow_natCard_sub_one_eq_one_of_isDiag_sl {N : ℕ} {F : Type} [Field F] [Finite F]
    {g : Matrix.SpecialLinearGroup (Fin N) F} (hg : (g : Matrix (Fin N) (Fin N) F).IsDiag) :
    g ^ (Nat.card F - 1) = 1 := by
  have : Fintype F := Fintype.ofFinite F
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    Nat.card_eq_fintype_card]
  exact pow_card_sub_one_eq_one_of_isDiag hg (by rw [g.2]; exact one_ne_zero)

end PSLHelpers

section PSpHelpers

open CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

private theorem elt_pow_natCast {F : Type} [Field F] {n : ℕ} (r : RootSubgroupIndex n) (c : F)
    (m : ℕ) : elt r c ^ m = elt r ((m : F) * c) := by
  induction m with
  | zero => simp [elt_zero]
  | succ k ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, elt_add]

private theorem elt_one_pow_char {F : Type} [Field F] {n p : ℕ} [Fact p.Prime] [CharP F p]
    (r : RootSubgroupIndex n) : elt r (1 : F) ^ p = 1 := by
  rw [elt_pow_natCast, CharP.cast_eq_zero, zero_mul, elt_zero]

private theorem commute_single_of_commute_transvection {ι F : Type} [Fintype ι] [DecidableEq ι]
    [CommRing F] {M : Matrix ι ι F} {a b : ι}
    (h : M * Matrix.transvection a b (1 : F) = Matrix.transvection a b (1 : F) * M) :
    Commute (Matrix.single a b (1 : F)) M := by
  have h' : M * (1 + Matrix.single a b (1 : F)) = (1 + Matrix.single a b (1 : F)) * M := by
    simpa [Matrix.transvection] using h
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h'
  exact (add_left_cancel h').symm

private theorem isDiag_of_forall_commute_root_psp {F : Type} [Field F] {n : ℕ} {M : StatedSp n F}
    (hpos : ∀ k, Commute M (elt (RootSubgroupIndex.positiveLong k) (1 : F)))
    (hneg : ∀ k, Commute M (elt (RootSubgroupIndex.negativeLong k) (1 : F))) :
    (mat n F M).IsDiag := by
  refine isDiag_of_forall_commute_single (M := mat n F M) ?_
  intro j
  rcases j with k | k
  · refine ⟨Sum.inr k, ?_⟩
    have h : mat n F M * Matrix.transvection (Sum.inl k) (Sum.inr k) (1 : F) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) (1 : F) * mat n F M := by
      simpa [map_mul, mat_elt_positiveLong] using congrArg (mat n F) (hpos k)
    exact commute_single_of_commute_transvection h
  · refine ⟨Sum.inl k, ?_⟩
    have h : mat n F M * Matrix.transvection (Sum.inr k) (Sum.inl k) (1 : F) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) (1 : F) * mat n F M := by
      simpa [map_mul, mat_elt_negativeLong] using congrArg (mat n F) (hneg k)
    exact commute_single_of_commute_transvection h

private theorem eq_one_of_mem_center_of_pow_eq_one {F : Type} [Field F] {n p : ℕ} [Fact p.Prime]
    [CharP F p] {z : StatedSp n F} (hz : z ∈ center (StatedSp n F)) (hzpow : z ^ p = 1) :
    z = 1 := by
  have hdiag : (mat n F z).IsDiag :=
    isDiag_of_forall_commute_root_psp
      (fun k => (Subgroup.mem_center_iff.mp hz
        (elt (RootSubgroupIndex.positiveLong k) (1 : F))).symm)
      (fun k => (Subgroup.mem_center_iff.mp hz
        (elt (RootSubgroupIndex.negativeLong k) (1 : F))).symm)
  have hmat : mat n F z = 1 :=
    eq_one_of_isDiag_of_pow_eq_one hdiag (by rw [← map_pow, hzpow, map_one])
  exact mat_injective (by rw [hmat, map_one])

end PSpHelpers

section PSUHelpers

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

private theorem isDiag_of_forall_commute_diagonal' {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {M : Matrix ι ι F}
    (h : ∀ i j, i ≠ j → ∃ t : ι → F, t i ≠ t j ∧ Commute (Matrix.diagonal t) M) :
    M.IsDiag := by
  intro i j hij
  obtain ⟨t, ht, hc⟩ := h i j hij
  exact TauCeti.apply_eq_zero_of_commute_diagonal hc ht

private theorem unitaryTorus_diag_ne {F : Type} [Field F] {N m : ℕ} {ε : F}
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    {a b : Fin N} (hab : a ≠ b) {k : Fin (m + 1)} (hk : k.val = a.val / 2) :
    (if a.val = 2 * k.val then ε else if a.val = 2 * k.val + 1 then ε⁻¹ else 1) ≠
      (if b.val = 2 * k.val then ε else if b.val = 2 * k.val + 1 then ε⁻¹ else 1) := by
  have hbne : b.val ≠ a.val := fun h => hab (Fin.ext h.symm)
  rw [hk]
  by_cases hae : a.val = 2 * (a.val / 2)
  · rw [if_pos hae]
    have hbe : b.val ≠ 2 * (a.val / 2) := by omega
    rw [if_neg hbe]
    by_cases hbo : b.val = 2 * (a.val / 2) + 1
    · rw [if_pos hbo]
      exact hεne
    · rw [if_neg hbo]
      exact hε1
  · rw [if_neg hae]
    have hao : a.val = 2 * (a.val / 2) + 1 := by omega
    rw [if_pos hao]
    have hbo : b.val ≠ 2 * (a.val / 2) + 1 := by omega
    rw [if_neg hbo]
    by_cases hbe : b.val = 2 * (a.val / 2)
    · rw [if_pos hbe]
      exact fun h => hεne h.symm
    · rw [if_neg hbe]
      exact hεinv1

private theorem blockMat_diagonal_two {F : Type} [Field F] {m tail : ℕ} {ε ε' : F}
    (k : Fin (m + 1)) :
    blockMat (2 * m + 1 + 1 + tail) (2 * k.val) (Matrix.diagonal ![ε, ε']) =
      Matrix.diagonal (fun a : Fin (2 * m + 1 + 1 + tail) =>
        if a.val = 2 * k.val then ε
        else if a.val = 2 * k.val + 1 then ε' else 1) := by
  ext a b
  rw [Matrix.diagonal_apply, blockMat_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases h0 : a.val = 2 * k.val
    · have hin : 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2 := by omega
      rw [dif_pos ⟨hin, hin⟩, if_pos h0]
      have hx : (⟨a.val - 2 * k.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp [h0])
      rw [hx]
      simp
    · by_cases h1 : a.val = 2 * k.val + 1
      · have hin : 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2 := by omega
        rw [dif_pos ⟨hin, hin⟩, if_neg h0, if_pos h1]
        have hx : (⟨a.val - 2 * k.val, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp [h1])
        rw [hx]
        simp
      · have hout : ¬ (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) := by omega
        rw [dif_neg (fun h => hout h.1), if_neg h0, if_neg h1, Matrix.one_apply_eq]
  · rw [if_neg hab]
    by_cases hin : (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) ∧
        (2 * k.val ≤ b.val ∧ b.val < 2 * k.val + 2)
    · rw [dif_pos hin]
      have hne : (⟨a.val - 2 * k.val, by omega⟩ : Fin 2) ≠
          ⟨b.val - 2 * k.val, by omega⟩ := by
        intro h
        apply hab
        apply Fin.ext
        have h' : a.val - 2 * k.val = b.val - 2 * k.val := congrArg Fin.val h
        omega
      rw [Matrix.diagonal_apply_ne _ hne]
    · rw [dif_neg hin, Matrix.one_apply_ne hab]

private theorem suMat_blockEmb_diag_eq {F : Type} [Field F] [Finite F] {p f m tail : ℕ}
    [Fact p.Prime] [CharP F p] {ε : F} {D : Su F p f 2}
    (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹]) (k : Fin (m + 1)) :
    suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) D) =
      Matrix.diagonal (fun a : Fin (2 * m + 1 + 1 + tail) =>
        if a.val = 2 * k.val then ε
        else if a.val = 2 * k.val + 1 then ε⁻¹ else 1) := by
  rw [suMat_blockEmb, hD, blockMat_diagonal_two]

private theorem isDiag_of_forall_commute_blockEmb_diag {F : Type} [Field F] [Finite F]
    {p f m tail : ℕ} [Fact p.Prime] [CharP F p] (htail : tail ≤ 1) {ε : F} {D : Su F p f 2}
    (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹])
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    {M : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F}
    (hM : ∀ k : Fin (m + 1),
      Commute (suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) D)) M) :
    M.IsDiag := by
  refine isDiag_of_forall_commute_diagonal' fun a b hab => ?_
  by_cases ha : a.val < 2 * m + 2
  · let k : Fin (m + 1) := ⟨a.val / 2, by omega⟩
    refine ⟨fun x => if x.val = 2 * k.val then ε
        else if x.val = 2 * k.val + 1 then ε⁻¹ else 1,
      unitaryTorus_diag_ne hε1 hεinv1 hεne hab rfl, ?_⟩
    rw [← suMat_blockEmb_diag_eq (tail := tail) hD k]
    exact hM k
  ·
    have hb : b.val < 2 * m + 2 := by
      have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
      have := a.isLt
      have := b.isLt
      omega
    let k : Fin (m + 1) := ⟨b.val / 2, by omega⟩
    refine ⟨fun x => if x.val = 2 * k.val then ε
        else if x.val = 2 * k.val + 1 then ε⁻¹ else 1,
      (unitaryTorus_diag_ne hε1 hεinv1 hεne (Ne.symm hab) rfl).symm, ?_⟩
    rw [← suMat_blockEmb_diag_eq (tail := tail) hD k]
    exact hM k

private theorem eq_one_of_mem_center_of_pow_eq_one_su {F : Type} [Field F] [Finite F]
    {p f m tail : ℕ} [Fact p.Prime] [CharP F p] (htail : tail ≤ 1) {ε : F} {D : Su F p f 2}
    (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹])
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    {z : Su F p f (2 * m + 1 + 1 + tail)}
    (hz : z ∈ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail))) (hzp : z ^ p = 1) :
    z = 1 := by
  have hdiag : (suMat z).IsDiag := by
    refine isDiag_of_forall_commute_blockEmb_diag htail hD hε1 hεinv1 hεne fun k => ?_
    have h := Subgroup.mem_center_iff.mp hz
      (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) D)
    have h' := congrArg suMat h
    simp only [suMat_mul] at h'
    exact h'
  have hmat : (suMat z) ^ p = 1 := by
    have h := map_pow (suMatHom F p f (2 * m + 1 + 1 + tail)) z p
    simp only [suMatHom_apply] at h
    rw [← h, hzp, suMat_one]
  have hz1 : suMat z = 1 := eq_one_of_isDiag_of_pow_eq_one hdiag hmat
  exact suMat_injective (by rw [hz1, suMat_one])

private theorem commute_of_pow_eq_one_unitaryFrameBlock {F : Type} [Field F] [Finite F]
    {p f m tail : ℕ} [Fact p.Prime] [CharP F p] (htail : tail ≤ 1) {X : Type} [Group X]
    {ε : F} {D : Su F p f 2} (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹])
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    {ψc : Su F p f (2 * m + 1 + 1 + tail) →* X}
    (hkerC : ψc.ker ≤ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)))
    {g : Su F p f (2 * m + 1 + 1 + tail)}
    (hxK : ∀ k : Fin (m + 1),
      ψc g ∈ Subgroup.centralizer ((unitaryFrameBlock F p f m k tail).map ψc : Set X))
    (k : Fin (m + 1)) {y : Su F p f (2 * m + 1 + 1 + tail)}
    (hy : y ∈ unitaryFrameBlock F p f m k tail) (hyp : y ^ p = 1) :
    Commute g y := by
  have hc : Commute (ψc y) (ψc g) :=
    Subgroup.mem_centralizer_iff.mp (hxK k) (ψc y) (Subgroup.mem_map_of_mem ψc hy)
  have hzy : g * y * g⁻¹ * y⁻¹ ∈ ψc.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← hc.eq]
    group
  have hzc : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)) :=
    hkerC hzy
  have hzpow : (g * y * g⁻¹ * y⁻¹) ^ p = 1 :=
    commutator_pow_eq_one_of_commute
      (Subgroup.mem_center_iff.mp hzc y).symm hyp
  have hz1 : g * y * g⁻¹ * y⁻¹ = 1 :=
    eq_one_of_mem_center_of_pow_eq_one_su htail hD hε1 hεinv1 hεne hzc hzpow
  have h1 : g * y * g⁻¹ = y := mul_inv_eq_one.mp hz1
  calc g * y = (g * y * g⁻¹) * g := by group
    _ = y * g := by rw [h1]

private theorem commute_of_mem_unitaryFrameBlock {F : Type} [Field F] [Finite F]
    {p f m tail : ℕ} [Fact p.Prime] [CharP F p] (htail : tail ≤ 1) {X : Type} [Group X]
    {ε : F} {D : Su F p f 2} (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹])
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    (hF : Nat.card F = (p ^ f) ^ 2)
    {ψc : Su F p f (2 * m + 1 + 1 + tail) →* X}
    (hkerC : ψc.ker ≤ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)))
    {g : Su F p f (2 * m + 1 + 1 + tail)}
    (hxK : ∀ k : Fin (m + 1),
      ψc g ∈ Subgroup.centralizer ((unitaryFrameBlock F p f m k tail).map ψc : Set X))
    (k : Fin (m + 1)) {y : Su F p f (2 * m + 1 + 1 + tail)}
    (hy : y ∈ unitaryFrameBlock F p f m k tail) :
    Commute g y := by
  obtain ⟨e⟩ := nonempty_equiv_sl2_unitaryFrameBlock (F := F) (p := p) (f := f)
    (m := m) (tail := tail) hF k
  let S : Subgroup (unitaryFrameBlock F p f m k tail) :=
    (Subgroup.centralizer ({g} : Set (Su F p f (2 * m + 1 + 1 + tail)))).comap
      (unitaryFrameBlock F p f m k tail).subtype
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← CFSG.LieType.HighestRoot.closure_pow_eq_one_eq_top_of_mulEquiv p e,
      Subgroup.closure_le]
    intro z hz
    simp only [S]
    change (z : Su F p f (2 * m + 1 + 1 + tail)) ∈
      Subgroup.centralizer ({g} : Set (Su F p f (2 * m + 1 + 1 + tail)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzpow : (z : Su F p f (2 * m + 1 + 1 + tail)) ^ p = 1 := by
      have := congrArg (fun w : unitaryFrameBlock F p f m k tail =>
        (w : Su F p f (2 * m + 1 + 1 + tail))) hz
      simpa using this
    exact (commute_of_pow_eq_one_unitaryFrameBlock htail hD hε1 hεinv1 hεne hkerC hxK k z.2
      hzpow).symm
  have hyS : (⟨y, hy⟩ : unitaryFrameBlock F p f m k tail) ∈ S := hS.symm ▸ Subgroup.mem_top _
  simp only [S] at hyS
  change (y : Su F p f (2 * m + 1 + 1 + tail)) ∈
    Subgroup.centralizer ({g} : Set (Su F p f (2 * m + 1 + 1 + tail))) at hyS
  rw [Subgroup.mem_centralizer_singleton_iff] at hyS
  exact hyS.symm

private theorem pow_card_sub_one_eq_one_of_commute_unitaryFrameBlock
    {F : Type} [Field F] [Finite F] {p f m tail : ℕ} [Fact p.Prime] [CharP F p]
    (htail : tail ≤ 1) {ε : F} {D : Su F p f 2} (hD : suMat D = Matrix.diagonal ![ε, ε⁻¹])
    (hε1 : ε ≠ 1) (hεinv1 : ε⁻¹ ≠ 1) (hεne : ε ≠ ε⁻¹)
    {g : Su F p f (2 * m + 1 + 1 + tail)}
    (hg : ∀ k : Fin (m + 1),
      Commute g (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) D)) :
    g ^ (Nat.card F - 1) = 1 := by
  have hdiag : (suMat g).IsDiag := by
    refine isDiag_of_forall_commute_blockEmb_diag htail hD hε1 hεinv1 hεne fun k => ?_
    have h := congrArg suMat (hg k)
    simp only [suMat_mul] at h
    exact h.symm
  have hdet : (suMat g).det ≠ 0 := by
    rw [det_suMat]
    exact one_ne_zero
  have : Fintype F := Fintype.ofFinite F
  have hmat : (suMat g) ^ (Nat.card F - 1) = 1 := by
    have := pow_card_sub_one_eq_one_of_isDiag (F := F) hdiag hdet
    simpa using this
  apply suMat_injective
  have h := map_pow (suMatHom F p f (2 * m + 1 + 1 + tail)) g (Nat.card F - 1)
  simp only [suMatHom_apply] at h
  rw [h, hmat, suMat_one]

private theorem pow_sq_sub_one_eq_one_of_forall_unitaryFrameBlock
    {X : Type} [Group X] {p m f tail : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (htail : tail ≤ 1)
    (ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + tail) →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + tail))) {x : X}
    (hx : ∀ k : Fin (m + 1), x ∈
      centralizer ((unitaryFrameBlock (GaloisField p (2 * f)) p f m k tail).map ψ : Set X)) :
    x ^ ((p ^ f) ^ 2 - 1) = 1 := by
  classical
  let F := GaloisField p (2 * f)
  obtain ⟨g, rfl⟩ := hψ x
  have hF : Nat.card F = (p ^ f) ^ 2 := by
    simpa [F] using CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hq3 : 3 ≤ p ^ f := by
    have := hp.out.two_le
    calc 3 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
  obtain ⟨ε, hε, hεsq⟩ := CFSG.GH74.Generic.BProg.B2.GenLocU3Good.exists_unit_sq_ne_one
    hF hq3
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h] at hε
    simp at hε
  have hε1 : ε ≠ 1 := by
    intro h
    exact hεsq (by simp [h])
  have hεinv1 : ε⁻¹ ≠ 1 := by
    intro h
    exact hε1 (inv_eq_one.mp h)
  have hεne : ε ≠ ε⁻¹ := by
    intro h
    have hsq : ε * ε = 1 := by
      have h' : ε * ε = ε * ε⁻¹ := congrArg (fun x => ε * x) h
      rwa [mul_inv_cancel₀ hε0] at h'
    exact hεsq hsq
  have hσ : unitaryInvolution F p f ε * ε = 1 := by
    rw [unitaryInvolution_apply]
    exact hε
  have hσinv : unitaryInvolution F p f ε⁻¹ * ε⁻¹ = 1 := by
    calc unitaryInvolution F p f ε⁻¹ * ε⁻¹
        = (unitaryInvolution F p f ε)⁻¹ * ε⁻¹ := by rw [map_inv₀]
      _ = (ε * unitaryInvolution F p f ε)⁻¹ := by rw [_root_.mul_inv_rev]
      _ = 1 := by rw [mul_comm ε, hσ, inv_one]
  have hdet : (Matrix.diagonal ![ε, ε⁻¹]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [hε0]
  have hiso : conjTr (unitaryInvolution F p f) (Matrix.diagonal ![ε, ε⁻¹]) *
      Matrix.diagonal ![ε, ε⁻¹] = 1 := by
    rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hσ
    · simpa using hσinv
  let D : Su F p f 2 := mkSU F p f (Matrix.diagonal ![ε, ε⁻¹]) hdet hiso
  have hD : suMat D = Matrix.diagonal ![ε, ε⁻¹] := suMat_mkSU hdet hiso
  have hcommBlock : ∀ k : Fin (m + 1),
      Commute g (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) D) := by
    intro k
    exact commute_of_mem_unitaryFrameBlock htail hD hε1 hεinv1 hεne hF hker hx k ⟨D, rfl⟩
  have hgpow : g ^ (Nat.card F - 1) = 1 :=
    pow_card_sub_one_eq_one_of_commute_unitaryFrameBlock htail hD hε1 hεinv1 hεne hcommBlock
  rw [← hF, ← map_pow, hgpow, map_one]

private theorem centralCover_conj {Y X : Type} [Group Y] [Group X] {ψ : Y →* X}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center Y) (c : X) :
    Function.Surjective ((MulAut.conj c).toMonoidHom.comp ψ) ∧
      ((MulAut.conj c).toMonoidHom.comp ψ).ker ≤ center Y := by
  refine ⟨(MulAut.conj c).surjective.comp hψ, fun y hy => hker ?_⟩
  rw [MonoidHom.mem_ker] at hy ⊢
  exact (MulAut.conj c).injective (by simpa using hy)

end PSUHelpers

section POmegaOddHelpers

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap
open scoped MatrixGroups



private theorem commute_map_of_commute_map_of_ker_le {G X Y : Type} [Group G] [Group X]
    [Group Y] {ψ : G →* X} {θ : G →* Y} (h : ψ.ker ≤ θ.ker) {a b : G}
    (hab : Commute (ψ a) (ψ b)) : Commute (θ a) (θ b) := by
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hab.eq]
    group
  have hθ := h hmem
  rw [MonoidHom.mem_ker] at hθ
  simp only [map_mul, map_inv] at hθ
  rw [Commute]
  calc θ a * θ b = (θ a * θ b * (θ a)⁻¹ * (θ b)⁻¹) * (θ b * θ a) := by group
    _ = θ b * θ a := by rw [hθ, one_mul]

private theorem forall_incl_eq_of_commute_oddPairFrame {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) {n r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {Fr : Frame (quadOdd n F)}
    {h : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ A : SL(2, F), h * Fr.La A = Fr.La A * h)
    (hR : ∀ A : SL(2, F), h * Fr.swap.La A = Fr.swap.La A * h) :
    ∀ X, h (Fr.incl X) = Fr.incl X := by
  have hg : h * Fr.La (-1) = Fr.La (-1) * h := hL (-1)
  obtain ⟨μ, hμ, hW⟩ := CFSG.ComponentClassification.HarrisLit.T1.S74.exists_smul_of_commute_La
    Fr h2 hhO hg hL hR
  have hv : Fr.incl (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h0
    apply one_ne_zero (α := Matrix (Fin 2) (Fin 2) F)
    exact Fr.incl_injective (by simpa using h0)
  have hμpow : μ ^ (r ^ a) = 1 := by
    have hsmul : ∀ k : ℕ, (h ^ k) (Fr.incl 1) = μ ^ k • Fr.incl 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hW, map_smul, ih, smul_smul, ← pow_succ']
    have h1 : μ ^ (r ^ a) • Fr.incl 1 = 1 • Fr.incl 1 := by
      rw [← hsmul (r ^ a), hpow]
      simp
    exact smul_left_injective F hv (by simpa using h1)
  have hodd : Odd (r ^ a) := (Nat.Prime.odd_of_ne_two hr hr2).pow
  have hμeq : μ ^ (r ^ a) = μ := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, show μ ^ 2 = 1 by rw [pow_two, hμ], one_pow, one_mul]
  have hμ1 : μ = 1 := by rw [← hμeq, hμpow]
  intro X
  rw [hW X, hμ1, one_smul]

private theorem fixes_pairs_of_commute_oddPairFrames {F : Type} [Field F]
    {n r a : ℕ} (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    {h : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F n j).La A = (oddOrthogonalPairFrame F n j).La A * h)
    (hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F n j).swap.La A =
        (oddOrthogonalPairFrame F n j).swap.La A * h) :
    ∀ i : Fin n, i.val < 2 * (n / 2) →
      h (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
  intro i hi
  have hlt : i.val / 2 < n / 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  let j : Fin (n / 2) := ⟨i.val / 2, hlt⟩
  have hcases : i.val = 2 * j.val ∨ i.val = 2 * j.val + 1 := by
    have hmod := Nat.mod_two_eq_zero_or_one i.val
    have hdm : 2 * (i.val / 2) + i.val % 2 = i.val := Nat.div_add_mod i.val 2
    have hj : (j : ℕ) = i.val / 2 := rfl
    rw [hj]
    rcases hmod with h0 | h1 <;> omega
  have hfix := forall_incl_eq_of_commute_oddPairFrame h2 hr hr2 hhO hpow
    (hL j) (hR j)
  have h1 : (oddOrthogonalPairFrame F n j).incl (Matrix.single 0 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h2' : (oddOrthogonalPairFrame F n j).incl (Matrix.single 1 1 1) =
      Pi.single (Sum.inr (Sum.inl ⟨2 * j.val, by omega⟩)) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h3 : (oddOrthogonalPairFrame F n j).incl (Matrix.single 0 1 (-1)) =
      Pi.single (Sum.inr (Sum.inl ⟨2 * j.val + 1, by omega⟩)) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  have h4 : (oddOrthogonalPairFrame F n j).incl (Matrix.single 1 0 1) =
      Pi.single (Sum.inl ⟨2 * j.val + 1, by omega⟩) (1 : F) := by
    rw [Frame.incl_apply]
    simp
    rfl
  rcases hcases with hcase | hcase
  · have hi' : i = ⟨2 * j.val, by omega⟩ := Fin.ext hcase
    rw [hi']
    refine ⟨?_, ?_⟩
    · have := hfix (Matrix.single 0 0 1)
      rwa [h1] at this
    · have := hfix (Matrix.single 1 1 1)
      rwa [h2'] at this
  · have hi' : i = ⟨2 * j.val + 1, by omega⟩ := Fin.ext hcase
    rw [hi']
    refine ⟨?_, ?_⟩
    · have := hfix (Matrix.single 1 0 1)
      rwa [h4] at this
    · have := hfix (Matrix.single 0 1 (-1))
      rwa [h3] at this

private theorem maps_residual_of_forall_fix_basis {F : Type} [Field F] {n : ℕ}
    {g : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F))
    (hfix : ∀ i : Fin n, i.val < 2 * (n / 2) →
      g (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      g (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1)
    {w : Fin n ⊕ Fin n ⊕ Unit → F}
    (hw : ∀ i : Fin n, i.val < 2 * (n / 2) →
      w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0) :
    ∀ i : Fin n, i.val < 2 * (n / 2) →
      (g w) (Sum.inl i) = 0 ∧ (g w) (Sum.inr (Sum.inl i)) = 0 := by
  intro i hi
  constructor
  · calc (g w) (Sum.inl i)
        = polar (quadOdd n F) (g w) (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          (CFSG.LieType.Universal.Spin.polar_quadOdd_single_inr_inl n F (g w) i).symm
      _ = polar (quadOdd n F) (g w) (g (Pi.single (Sum.inr (Sum.inl i)) 1)) := by
          rw [(hfix i hi).2]
      _ = polar (quadOdd n F) w (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inl i) :=
          CFSG.LieType.Universal.Spin.polar_quadOdd_single_inr_inl n F w i
      _ = 0 := (hw i hi).1
  · calc (g w) (Sum.inr (Sum.inl i))
        = polar (quadOdd n F) (g w) (Pi.single (Sum.inl i) 1) :=
          (CFSG.LieType.Universal.Spin.polar_quadOdd_single_inl n F (g w) i).symm
      _ = polar (quadOdd n F) (g w) (g (Pi.single (Sum.inl i) 1)) := by
          rw [(hfix i hi).1]
      _ = polar (quadOdd n F) w (Pi.single (Sum.inl i) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO w _
      _ = w (Sum.inr (Sum.inl i)) :=
          CFSG.LieType.Universal.Spin.polar_quadOdd_single_inl n F w i
      _ = 0 := (hw i hi).2

private theorem eq_one_of_commute_oddPairFrames_even {F : Type} [Field F] {m r a : ℕ}
    (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    {h : (Fin (2 * m) ⊕ Fin (2 * m) ⊕ Unit → F) ≃ₗ[F]
      (Fin (2 * m) ⊕ Fin (2 * m) ⊕ Unit → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (2 * m) F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((2 * m) / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F (2 * m) j).La A =
        (oddOrthogonalPairFrame F (2 * m) j).La A * h)
    (hR : ∀ (j : Fin ((2 * m) / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F (2 * m) j).swap.La A =
        (oddOrthogonalPairFrame F (2 * m) j).swap.La A * h) :
    h = 1 := by
  have hpair := fixes_pairs_of_commute_oddPairFrames h2 hr hr2 hhO hpow hL hR
  have hall : ∀ i : Fin (2 * m), i.val < 2 * ((2 * m) / 2) := by
    intro i
    rw [show (2 * m) / 2 = m by omega]
    omega
  let z : Fin (2 * m) ⊕ Fin (2 * m) ⊕ Unit → F := oddZ (2 * m) F
  have hz_e : ∀ i : Fin (2 * m), (h z) (Sum.inl i) = 0 := by
    intro i
    have hi := hall i
    calc (h z) (Sum.inl i)
        = polar (quadOdd (2 * m) F) (h z) (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          (polar_quadOdd_single_inr_inl (2 * m) F (h z) i).symm
      _ = polar (quadOdd (2 * m) F) (h z) (h (Pi.single (Sum.inr (Sum.inl i)) 1)) := by
          rw [(hpair i hi).2]
      _ = polar (quadOdd (2 * m) F) z (Pi.single (Sum.inr (Sum.inl i)) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hhO z _
      _ = z (Sum.inl i) := polar_quadOdd_single_inr_inl (2 * m) F z i
      _ = 0 := by simp [z, oddZ]
  have hz_f : ∀ i : Fin (2 * m), (h z) (Sum.inr (Sum.inl i)) = 0 := by
    intro i
    have hi := hall i
    calc (h z) (Sum.inr (Sum.inl i))
        = polar (quadOdd (2 * m) F) (h z) (Pi.single (Sum.inl i) 1) :=
          (polar_quadOdd_single_inl (2 * m) F (h z) i).symm
      _ = polar (quadOdd (2 * m) F) (h z) (h (Pi.single (Sum.inl i) 1)) := by
          rw [(hpair i hi).1]
      _ = polar (quadOdd (2 * m) F) z (Pi.single (Sum.inl i) 1) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hhO z _
      _ = z (Sum.inr (Sum.inl i)) := polar_quadOdd_single_inl (2 * m) F z i
      _ = 0 := by simp [z, oddZ]
  let c : F := (h z) (Sum.inr (Sum.inr ()))
  have hz_form : h z = c • z := by
    ext x
    rcases x with i | i | u
    · rw [hz_e i]
      have hz0 : z (Sum.inl i) = 0 := by simp [z, oddZ]
      simp [Pi.smul_apply, smul_eq_mul, hz0]
    · rw [hz_f i]
      have hz0 : z (Sum.inr (Sum.inl i)) = 0 := by simp [z, oddZ]
      simp [Pi.smul_apply, smul_eq_mul, hz0]
    · cases u
      simp [c, z, oddZ, Pi.smul_apply, smul_eq_mul]
  have hc : c * c = 1 := by
    have hmap := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hhO) z
    calc c * c = quadOdd (2 * m) F (c • z) := by
          rw [QuadraticMap.map_smul, quadOdd_oddZ, smul_eq_mul, mul_one]
      _ = quadOdd (2 * m) F (h z) := by rw [hz_form]
      _ = quadOdd (2 * m) F z := hmap
      _ = 1 := by simpa [z] using quadOdd_oddZ (2 * m) F
  have hodd : Odd (r ^ a) := (Nat.Prime.odd_of_ne_two hr hr2).pow
  have hcpow : c ^ (r ^ a) = c := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, show c ^ 2 = 1 by rw [pow_two, hc], one_pow, one_mul]
  have hsmul : ∀ k : ℕ, (h ^ k) z = c ^ k • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, LinearEquiv.mul_apply, hz_form, map_smul, ih, smul_smul, ← pow_succ']
  have hz : h z = z := by
    have h1 := hsmul (r ^ a)
    rw [hpow, hcpow, ← hz_form] at h1
    exact h1.symm
  have hfix_all : ∀ x : Fin (2 * m) ⊕ Fin (2 * m) ⊕ Unit,
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i | u)
    · exact (hpair i (hall i)).1
    · exact (hpair i (hall i)).2
    · cases u
      simpa [z, oddZ] using hz
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v



private noncomputable def oddResidualCoord (m : ℕ) (F : Type) [Field F] :
    (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F) →ₗ[F] (Fin 1 ⊕ Fin 1 ⊕ Unit → F) where
  toFun v := fun x =>
    match x with
    | Sum.inl _ => v (Sum.inl ⟨2 * m, by omega⟩)
    | Sum.inr (Sum.inl _) => v (Sum.inr (Sum.inl ⟨2 * m, by omega⟩))
    | Sum.inr (Sum.inr _) => v (Sum.inr (Sum.inr ()))
  map_add' v w := by
    funext x
    rcases x with i | i | u <;> simp
  map_smul' c v := by
    funext x
    rcases x with i | i | u <;> simp

private noncomputable def oddResidualIncl (m : ℕ) (F : Type) [Field F] :
    (Fin 1 ⊕ Fin 1 ⊕ Unit → F) →ₗ[F] (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F) where
  toFun t := fun x =>
    match x with
    | Sum.inl i => if i.val = 2 * m then t (Sum.inl 0) else 0
    | Sum.inr (Sum.inl i) => if i.val = 2 * m then t (Sum.inr (Sum.inl 0)) else 0
    | Sum.inr (Sum.inr _) => t (Sum.inr (Sum.inr ()))
  map_add' t s := by
    funext x
    rcases x with i | i | u
    · by_cases hi : i.val = 2 * m <;> simp [hi]
    · by_cases hi : i.val = 2 * m <;> simp [hi]
    · simp
  map_smul' c t := by
    funext x
    rcases x with i | i | u
    · by_cases hi : i.val = 2 * m <;> simp [hi]
    · by_cases hi : i.val = 2 * m <;> simp [hi]
    · simp

private noncomputable def oddResidualSub (m : ℕ) (F : Type) [Field F] :
    Submodule F (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F) where
  carrier := {w | ∀ i : Fin (2 * m + 1), i.val < 2 * m →
    w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0}
  zero_mem' := by
    intro i _
    simp
  add_mem' {a b} ha hb := by
    intro i hi
    rw [Pi.add_apply, Pi.add_apply, (ha i hi).1, (hb i hi).1, (ha i hi).2, (hb i hi).2]
    simp
  smul_mem' c a ha := by
    intro i hi
    rw [Pi.smul_apply, Pi.smul_apply, (ha i hi).1, (ha i hi).2]
    simp

private theorem mem_oddResidualSub {m : ℕ} {F : Type} [Field F]
    {w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F} :
    w ∈ oddResidualSub m F ↔ ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      w (Sum.inl i) = 0 ∧ w (Sum.inr (Sum.inl i)) = 0 := Iff.rfl

private theorem oddResidualCoord_comp_incl (m : ℕ) (F : Type) [Field F]
    (t : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    oddResidualCoord m F (oddResidualIncl m F t) = t := by
  funext x
  rcases x with i | i | u
  · have hi : i = 0 := Fin.fin_one_eq_zero i
    rw [hi]
    simp [oddResidualCoord, oddResidualIncl]
  · have hi : i = 0 := Fin.fin_one_eq_zero i
    rw [hi]
    simp [oddResidualCoord, oddResidualIncl]
  · simp [oddResidualCoord, oddResidualIncl]

private theorem oddResidualIncl_injective (m : ℕ) (F : Type) [Field F] :
    Function.Injective (oddResidualIncl m F) := by
  intro a b h
  have := congrArg (oddResidualCoord m F) h
  simpa [oddResidualCoord_comp_incl] using this

private theorem oddResidualIncl_mem (m : ℕ) (F : Type) [Field F]
    (t : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    oddResidualIncl m F t ∈ oddResidualSub m F := by
  intro i hi
  have hne : i.val ≠ 2 * m := by omega
  simp [oddResidualIncl, hne]

private theorem oddResidualIncl_coord_of_mem (m : ℕ) (F : Type) [Field F]
    {w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F}
    (hw : w ∈ oddResidualSub m F) :
    oddResidualIncl m F (oddResidualCoord m F w) = w := by
  funext x
  rcases x with i | i | u
  · by_cases hi : i.val = 2 * m
    · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
      rw [hi']
      simp [oddResidualIncl, oddResidualCoord]
    · have hlt : i.val < 2 * m := by omega
      have hw0 := (mem_oddResidualSub.mp hw) i hlt
      simp [oddResidualIncl, oddResidualCoord, hi, hw0.1]
  · by_cases hi : i.val = 2 * m
    · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
      rw [hi']
      simp [oddResidualIncl, oddResidualCoord]
    · have hlt : i.val < 2 * m := by omega
      have hw0 := (mem_oddResidualSub.mp hw) i hlt
      simp [oddResidualIncl, oddResidualCoord, hi, hw0.2]
  · simp [oddResidualIncl, oddResidualCoord]

private theorem oddResidualSub_eq_range (m : ℕ) (F : Type) [Field F] :
    oddResidualSub m F = LinearMap.range (oddResidualIncl m F) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    exact ⟨oddResidualCoord m F w, oddResidualIncl_coord_of_mem m F hw⟩
  · rintro _ ⟨t, rfl⟩
    exact oddResidualIncl_mem m F t

private theorem finrank_oddResidualSub (m : ℕ) (F : Type) [Field F] :
    Module.finrank F (oddResidualSub m F) = 3 := by
  rw [oddResidualSub_eq_range,
    LinearMap.finrank_range_of_inj (oddResidualIncl_injective m F),
    Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_sum]

private theorem isCompl_oddResidualSub_ker (m : ℕ) (F : Type) [Field F] :
    IsCompl (oddResidualSub m F) (LinearMap.ker (oddResidualCoord m F)) := by
  refine IsCompl.mk ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwW, hwK⟩ := hw
    rw [LinearMap.mem_ker] at hwK
    funext x
    rcases x with i | i | u
    · by_cases hi : i.val = 2 * m
      · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
        rw [hi']
        simp only [Pi.zero_apply]
        have := congrFun hwK (Sum.inl (0 : Fin 1))
        simpa [oddResidualCoord] using this
      · have hlt : i.val < 2 * m := by omega
        exact (mem_oddResidualSub.mp hwW) i hlt |>.1
    · by_cases hi : i.val = 2 * m
      · have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
        rw [hi']
        simp only [Pi.zero_apply]
        have := congrFun hwK (Sum.inr (Sum.inl (0 : Fin 1)))
        simpa [oddResidualCoord] using this
      · have hlt : i.val < 2 * m := by omega
        exact (mem_oddResidualSub.mp hwW) i hlt |>.2
    · simp only [Pi.zero_apply]
      have := congrFun hwK (Sum.inr (Sum.inr ()))
      simpa [oddResidualCoord] using this
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h1 : v - oddResidualIncl m F (oddResidualCoord m F v) ∈
        LinearMap.ker (oddResidualCoord m F) := by
      rw [LinearMap.mem_ker, map_sub, oddResidualCoord_comp_incl, sub_self]
    refine Submodule.mem_sup.mpr ⟨oddResidualIncl m F (oddResidualCoord m F v),
      oddResidualIncl_mem m F _, v - oddResidualIncl m F (oddResidualCoord m F v), h1, ?_⟩
    abel

private theorem orthogonal_oddResidualSub_ker (m : ℕ) (F : Type) [Field F]
    {w u : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F}
    (hw : w ∈ oddResidualSub m F) (hu : u ∈ LinearMap.ker (oddResidualCoord m F)) :
    polar (quadOdd (2 * m + 1) F) w u = 0 := by
  rw [polar_quadOdd]
  have hu0 : ∀ i : Fin (2 * m + 1), i.val = 2 * m → u (Sum.inl i) = 0 := by
    intro i hi
    have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
    rw [hi']
    have := congrFun (LinearMap.mem_ker.mp hu) (Sum.inl (0 : Fin 1))
    simpa [oddResidualCoord] using this
  have hu1 : ∀ i : Fin (2 * m + 1), i.val = 2 * m → u (Sum.inr (Sum.inl i)) = 0 := by
    intro i hi
    have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hi
    rw [hi']
    have := congrFun (LinearMap.mem_ker.mp hu) (Sum.inr (Sum.inl (0 : Fin 1)))
    simpa [oddResidualCoord] using this
  have huz : u (Sum.inr (Sum.inr ())) = 0 := by
    have := congrFun (LinearMap.mem_ker.mp hu) (Sum.inr (Sum.inr ()))
    simpa [oddResidualCoord] using this
  have hsum : ∑ i : Fin (2 * m + 1),
      (w (Sum.inl i) * u (Sum.inr (Sum.inl i)) + u (Sum.inl i) * w (Sum.inr (Sum.inl i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val = 2 * m
    · rw [hu0 i hi, hu1 i hi]
      simp
    · have hlt : i.val < 2 * m := by omega
      rw [(mem_oddResidualSub.mp hw) i hlt |>.1, (mem_oddResidualSub.mp hw) i hlt |>.2]
      simp
  rw [hsum, huz]
  ring

private theorem ringChar_ne_two_of_two_ne_zero {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    ringChar F ≠ 2 := by
  intro h
  exact h2 ((ringChar.spec F 2).2 (h ▸ dvd_rfl))

private theorem card_orthogonalGroup_oddResidual (m : ℕ) (F : Type) [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadOdd (2 * m + 1) F).comp (oddResidualSub m F).subtype)) =
      2 * Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hQ := nondegenerate_polarBilin_quadOdd (2 * m + 1) F h2
  have hc := isCompl_oddResidualSub_ker m F
  have horth : ∀ w ∈ oddResidualSub m F,
      ∀ u ∈ LinearMap.ker (oddResidualCoord m F), polar (quadOdd (2 * m + 1) F) w u = 0 :=
    fun w hw u hu => orthogonal_oddResidualSub_ker m F hw hu
  have hQ' := CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype hQ hc horth
  have hdim : Module.finrank F (oddResidualSub m F) = 2 * 1 + 1 := by
    rw [finrank_oddResidualSub]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd
    (ringChar_ne_two_of_two_ne_zero h2) hQ' hdim
  rw [Finset.Icc_self, Finset.prod_singleton] at h
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq1
  have hcast : ((2 * Nat.card F * (Nat.card F ^ 2 - 1) : ℕ) : ℤ) =
      2 * (Nat.card F : ℤ) ^ 1 ^ 2 * (((Nat.card F : ℤ) ^ 2) ^ 1 - 1) := by
    push_cast [hq2]
    ring
  rw [← hcast] at h
  exact_mod_cast h

private theorem eq_one_of_commute_oddPairFrames_odd {F : Type} [Field F] [Finite F]
    {m r a : ℕ} (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    {h : (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F) ≃ₗ[F]
      (Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (2 * m + 1) F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin ((2 * m + 1) / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F (2 * m + 1) j).La A =
        (oddOrthogonalPairFrame F (2 * m + 1) j).La A * h)
    (hR : ∀ (j : Fin ((2 * m + 1) / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F (2 * m + 1) j).swap.La A =
        (oddOrthogonalPairFrame F (2 * m + 1) j).swap.La A * h) :
    h = 1 := by
  have hlt2 : 2 * ((2 * m + 1) / 2) = 2 * m := by omega
  have hpair := fixes_pairs_of_commute_oddPairFrames h2 hr hr2 hhO hpow hL hR
  have hpair' : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      h (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 :=
    fun i hi => hpair i (by rw [hlt2]; exact hi)
  have hfixinv : ∀ i : Fin (2 * m + 1), i.val < 2 * m →
      h⁻¹ (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      h⁻¹ (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h1 : h⁻¹ (h (Pi.single (Sum.inl i) 1)) = Pi.single (Sum.inl i) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair' i hi).1] at h1
      exact h1
    · have h1 : h⁻¹ (h (Pi.single (Sum.inr (Sum.inl i)) 1)) =
          Pi.single (Sum.inr (Sum.inl i)) 1 :=
        LinearEquiv.symm_apply_apply h _
      rw [(hpair' i hi).2] at h1
      exact h1
  let W₀ := oddResidualSub m F
  have hsta : h ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub W₀ := by
    intro x
    constructor
    · intro hx
      have hx' : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 :=
        fun i hi => hx i (by rw [hlt2] at hi; exact hi)
      have hx'' := maps_residual_of_forall_fix_basis hhO
        (fun i hi => hpair' i (by rw [hlt2] at hi; exact hi)) hx'
      exact fun i hi => hx'' i (by rw [hlt2]; exact hi)
    · intro hx
      have hx' : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          (h x) (Sum.inl i) = 0 ∧ (h x) (Sum.inr (Sum.inl i)) = 0 :=
        fun i hi => hx i (by rw [hlt2] at hi; exact hi)
      have hx'' := maps_residual_of_forall_fix_basis (Subgroup.inv_mem _ hhO)
        (fun i hi => hfixinv i (by rw [hlt2] at hi; exact hi)) hx'
      have hx3 : ∀ i : Fin (2 * m + 1), i.val < 2 * ((2 * m + 1) / 2) →
          x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
        simpa [LinearEquiv.symm_apply_apply] using hx''
      exact fun i hi => hx3 i (by rw [hlt2]; exact hi)
  let ν : W₀ ≃ₗ[F] W₀ := CFSG.ClassicalGroups.Orthogonal.Small.resHom W₀ ⟨h, hsta⟩
  have hνO : ν ∈ TauCeti.QuadraticMap.orthogonalGroup
      ((quadOdd (2 * m + 1) F).comp W₀.subtype) :=
    CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup hhO hsta
  have hνpow : ν ^ (r ^ a) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hsta]
    rw [hpow]
    rfl
  have hcard := card_orthogonalGroup_oddResidual m F h2
  have hnotdvd : ¬ r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadOdd (2 * m + 1) F).comp W₀.subtype)) := by
    rw [hcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h2q | hq
    · rcases (Nat.Prime.dvd_mul hr).1 h2q with h2r | hqr
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2r)
      · exact hrq (dvd_mul_of_dvd_left hqr _)
    · exact hrq (dvd_mul_of_dvd_right hq _)
  have hcopN : Nat.Coprime (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      ((quadOdd (2 * m + 1) F).comp W₀.subtype))) (r ^ a) := by
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hnotdvd).symm.pow_right a
  let ν₀ : TauCeti.QuadraticMap.orthogonalGroup ((quadOdd (2 * m + 1) F).comp W₀.subtype) :=
    ⟨ν, hνO⟩
  have hν₀pow : ν₀ ^ (r ^ a) = 1 := Subtype.ext hνpow
  have hν1 : ν = 1 := by
    have hdvd : orderOf ν₀ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        ((quadOdd (2 * m + 1) F).comp W₀.subtype)) := orderOf_dvd_natCard ν₀
    have hcop : Nat.Coprime (orderOf ν₀) (r ^ a) := hcopN.of_dvd_left hdvd
    have h1 : ν₀ = 1 := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hν₀pow))
    exact Subtype.ext_iff.mp h1
  have hfixW : ∀ w : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit → F, w ∈ W₀ → h w = w := by
    intro w hw
    have h1 : ν ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hν1]; rfl
    have h2 := congrArg Subtype.val h1
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply] at h2
    exact h2
  have hfix_all : ∀ x : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit,
      h (Pi.single x 1) = Pi.single x 1 := by
    rintro (i | i | u)
    · by_cases hi : i.val < 2 * m
      · exact (hpair' i hi).1
      · have hge : i.val = 2 * m := by have := i.isLt; omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inl j : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit) ≠
            Sum.inl ⟨2 * m, by omega⟩ := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
    · by_cases hi : i.val < 2 * m
      · exact (hpair' i hi).2
      · have hge : i.val = 2 * m := by have := i.isLt; omega
        have hi' : i = ⟨2 * m, by omega⟩ := Fin.ext hge
        rw [hi']
        refine hfixW _ ?_
        intro j hj
        have hne : (Sum.inr (Sum.inl j) : Fin (2 * m + 1) ⊕ Fin (2 * m + 1) ⊕ Unit) ≠
            Sum.inr (Sum.inl ⟨2 * m, by omega⟩) := by
          simp [Fin.ext_iff]
          omega
        simp [hne]
    · cases u
      refine hfixW _ ?_
      intro j hj
      simp
  have hlin : h.toLinearMap = 1 := by
    refine LinearMap.pi_ext fun x c' => ?_
    have hsingle : Pi.single x c' = c' • Pi.single x (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    calc h (Pi.single x c') = h (c' • Pi.single x (1 : F)) := by rw [hsingle]
      _ = c' • h (Pi.single x 1) := map_smul h c' _
      _ = c' • Pi.single x 1 := by rw [hfix_all x]
      _ = Pi.single x c' := hsingle.symm
  exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun hlin v


private theorem eq_one_of_commute_oddPairFrames {F : Type} [Field F] [Finite F] {n r a : ℕ}
    (h2 : (2 : F) ≠ 0) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1))
    {h : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F))
    (hpow : h ^ (r ^ a) = 1)
    (hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F n j).La A = (oddOrthogonalPairFrame F n j).La A * h)
    (hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      h * (oddOrthogonalPairFrame F n j).swap.La A =
        (oddOrthogonalPairFrame F n j).swap.La A * h) :
    h = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact eq_one_of_commute_oddPairFrames_even h2 hr hr2 hhO hpow hL hR
  · exact eq_one_of_commute_oddPairFrames_odd h2 hr hr2 hrq hhO hpow hL hR

end POmegaOddHelpers


theorem pow_sub_one_eq_one_of_forall_funSet_psl_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1) p f)
    (hX : LieModel X .PSL (2 * m + 1 + 1) p f) (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ (p ^ f - 1) = 1 := by
  classical
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1) p f Fact.out hp2 (by trivial) hadm X hX
  let ψ : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) (GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) (GaloisField p f)) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_even hp2 hm hadm hX ψ hψ hker P
  let F := GaloisField p f
  let ψc : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) F →* X :=
    (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) F) := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k).map ψc) := by
    simpa [F, ψc, Subgroup.map_map] using hfull
  obtain ⟨g, rfl⟩ := hψc x
  have hxK : ∀ k, ψc g ∈ centralizer ((linearFrameBlock F m k).map ψc : Set X) :=
    fun k => hx _ (by rw [hfull']; exact ⟨k, rfl⟩)
  have hfr : ∀ (k : Fin (m + 1)) (a b : Fin (2 * m + 1 + 1)) (hab : a ≠ b),
      a.val = 2 * k.val ∧ b.val = 2 * k.val + 1 ∨ a.val = 2 * k.val + 1 ∧ b.val = 2 * k.val →
      Commute (ψc g) (ψc (Matrix.SpecialLinearGroup.transvection hab (1 : F))) := by
    intro k a b hab hab'
    have hmem : Matrix.SpecialLinearGroup.transvection hab (1 : F) ∈ linearFrameBlock F m k := by
      let i : Fin (2 * m + 1) := ⟨2 * k.val, by omega⟩
      rcases hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain rfl : a = i.castSucc := Fin.ext ha
        obtain rfl : b = i.succ := Fin.ext hb
        exact ⟨_, CFSG.ClassicalInvolution.WeakCT.blockSL2_transvection_up i (1 : F)⟩
      · obtain rfl : a = i.succ := Fin.ext ha
        obtain rfl : b = i.castSucc := Fin.ext hb
        exact ⟨_, CFSG.ClassicalInvolution.WeakCT.blockSL2_transvection_down i (1 : F)⟩
    exact (show Commute (ψc _) (ψc g) from (Subgroup.mem_centralizer_iff.mp (hxK k)) _
      (Subgroup.mem_map_of_mem ψc hmem)).symm
  have hdiag : ((g : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) F) :
      Matrix (Fin (2 * m + 1 + 1)) (Fin (2 * m + 1 + 1)) F).IsDiag := by
    refine isDiag_of_commute_map_transvection hkerC fun k l _ => ?_
    have hl := l.isLt
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' l.val
    · exact ⟨l, ⟨2 * j + 1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega, Or.inl rfl,
        hfr ⟨j, by omega⟩ _ _ _ (Or.inl ⟨hj, rfl⟩)⟩
    · exact ⟨l, ⟨2 * j, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega, Or.inl rfl,
        hfr ⟨j, by omega⟩ _ _ _ (Or.inr ⟨hj, rfl⟩)⟩
  have hcard : Nat.card F = p ^ f := by
    simpa [F] using GaloisField.card p f (by have := hadm.2.1; omega)
  rw [← map_pow ψc, ← hcard, pow_natCard_sub_one_eq_one_of_isDiag_sl hdiag, map_one]

theorem pow_sub_one_eq_one_of_forall_funSet_psl_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) p f)
    (hX : LieModel X .PSL (2 * m + 1 + 1 + 1) p f) (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ (p ^ f - 1) = 1 := by
  classical
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1 + 1) p f Fact.out hp2 (by trivial) hadm X hX
  let ψ : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) (GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) (GaloisField p f)) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_odd hp2 hm hadm hX ψ hψ hker P
  let F := GaloisField p f
  let ψc : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) F →* X :=
    (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) F) := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k 1).map ψc) := by
    simpa [F, ψc, Subgroup.map_map] using hfull
  obtain ⟨g, rfl⟩ := hψc x
  have hxK : ∀ k, ψc g ∈ centralizer ((linearFrameBlock F m k 1).map ψc : Set X) :=
    fun k => hx _ (by rw [hfull']; exact ⟨k, rfl⟩)
  have hfr : ∀ (k : Fin (m + 1)) (a b : Fin (2 * m + 1 + 1 + 1)) (hab : a ≠ b),
      a.val = 2 * k.val ∧ b.val = 2 * k.val + 1 ∨ a.val = 2 * k.val + 1 ∧ b.val = 2 * k.val →
      Commute (ψc g) (ψc (Matrix.SpecialLinearGroup.transvection hab (1 : F))) := by
    intro k a b hab hab'
    have hmem : Matrix.SpecialLinearGroup.transvection hab (1 : F) ∈ linearFrameBlock F m k 1 := by
      let i : Fin (2 * m + 1 + 1) := ⟨2 * k.val, by omega⟩
      rcases hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain rfl : a = i.castSucc := Fin.ext ha
        obtain rfl : b = i.succ := Fin.ext hb
        exact ⟨_, CFSG.ClassicalInvolution.WeakCT.blockSL2_transvection_up i (1 : F)⟩
      · obtain rfl : a = i.succ := Fin.ext ha
        obtain rfl : b = i.castSucc := Fin.ext hb
        exact ⟨_, CFSG.ClassicalInvolution.WeakCT.blockSL2_transvection_down i (1 : F)⟩
    exact (show Commute (ψc _) (ψc g) from (Subgroup.mem_centralizer_iff.mp (hxK k)) _
      (Subgroup.mem_map_of_mem ψc hmem)).symm
  have hdiag : ((g : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) F) :
      Matrix (Fin (2 * m + 1 + 1 + 1)) (Fin (2 * m + 1 + 1 + 1)) F).IsDiag := by
    refine isDiag_of_commute_map_transvection hkerC fun k l hkl => ?_
    have hl := l.isLt
    have hk := k.isLt
    have hkl' : k.val ≠ l.val := fun h => hkl (Fin.ext h)
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' l.val
    · by_cases hjm : j < m + 1
      · exact ⟨l, ⟨2 * j + 1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega, Or.inl rfl,
          hfr ⟨j, hjm⟩ _ _ _ (Or.inl ⟨hj, rfl⟩)⟩
      ·
        obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k.val
        · exact ⟨⟨2 * i + 1, by omega⟩, k, fun h => by simp [Fin.ext_iff] at h; omega,
            Or.inr rfl, hfr ⟨i, by omega⟩ _ _ _ (Or.inr ⟨rfl, hi⟩)⟩
        · exact ⟨⟨2 * i, by omega⟩, k, fun h => by simp [Fin.ext_iff] at h; omega,
            Or.inr rfl, hfr ⟨i, by omega⟩ _ _ _ (Or.inl ⟨rfl, hi⟩)⟩
    · exact ⟨l, ⟨2 * j, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega, Or.inl rfl,
        hfr ⟨j, by omega⟩ _ _ _ (Or.inr ⟨hj, rfl⟩)⟩
  have hcard : Nat.card F = p ^ f := by
    simpa [F] using GaloisField.card p f (by have := hadm.2.1; omega)
  rw [← map_pow ψc, ← hcard, pow_natCard_sub_one_eq_one_of_isDiag_sl hdiag, map_one]

section PSUProof

open CFSG.ClassicalInvolution.Phan

private theorem exists_centralCover_su
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (hX : LieModel X .PSU n p f)
    (eU : (CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p f hp.out).K ≃*
      Su (GaloisField p (2 * f)) p f n) :
    ∃ ψ : Su (GaloisField p (2 * f)) p f n →* X, Function.Surjective ψ ∧
      ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f n) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU n p f hp.out hp2 (by trivial) hadm X hX
  refine ⟨ψ0.comp eU.symm.toMonoidHom, hψ0.comp eU.symm.surjective, ?_⟩
  intro y hy
  have hy' : eU.symm y ∈ center (CFSG.ClassicalInvolution.Generic.modelUniv
      .PSU n p f hp.out).K := hker0 hy
  rw [Subgroup.mem_center_iff] at hy' ⊢
  intro z
  apply eU.symm.injective
  simpa only [map_mul] using hy' (eU.symm z)

theorem pow_sq_sub_one_eq_one_of_forall_funSet_psu_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1) p f)
    (hX : LieModel X .PSU (2 * m + 1 + 1) p f) (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ ((p ^ f) ^ 2 - 1) = 1 := by
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨ψ, hψ, hker⟩ := exists_centralCover_su hp2 hadm hX eU
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_even hp2 hm hadm hX
    eU heU ψ hψ hker P
  obtain ⟨hψc, hkerC⟩ := centralCover_conj hψ hker c
  refine pow_sq_sub_one_eq_one_of_forall_unitaryFrameBlock (tail := 0) hp2 hadm.2.1
    (Nat.zero_le 1) _ hψc hkerC fun k => hx _ ?_
  rw [hfull]
  exact ⟨k, Subgroup.map_map ..⟩

theorem pow_sq_sub_one_eq_one_of_forall_funSet_psu_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) p f)
    (hX : LieModel X .PSU (2 * m + 1 + 1 + 1) p f) (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ ((p ^ f) ^ 2 - 1) = 1 := by
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨ψ, hψ, hker⟩ := exists_centralCover_su hp2 hadm hX eU
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_odd hp2 hm hadm hX
    eU heU ψ hψ hker P
  obtain ⟨hψc, hkerC⟩ := centralCover_conj hψ hker c
  refine pow_sq_sub_one_eq_one_of_forall_unitaryFrameBlock (tail := 1) hp2 hadm.2.1
    le_rfl _ hψc hkerC fun k => hx _ ?_
  rw [hfull]
  exact ⟨k, Subgroup.map_map ..⟩

end PSUProof

section PSpProof

open CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

theorem pow_sub_one_eq_one_of_forall_funSet_psp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f)
    (hX : LieModel X .PSp n p f) (P : Sylow 2 X) {x : X}
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x ^ (p ^ f - 1) = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSp n p f hp hp2 (by trivial) hadm X hX
  let F := GaloisField p f
  have : Fintype F := Fintype.ofFinite F
  let ψ : StatedSp n F →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center (StatedSp n F) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psp hp2 hadm hX ψ hψ hker P
  let ψc : StatedSp n F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (StatedSp n F) := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin n => (longRootSp2 F n k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  obtain ⟨g, hg⟩ := hψc x
  have hmem_pos : ∀ k : Fin n,
      elt (RootSubgroupIndex.positiveLong k) (1 : F) ∈ longRootSp2 F n k :=
    fun k => ⟨sl2Upper 1, longBlock_sl2Upper k 1⟩
  have hmem_neg : ∀ k : Fin n,
      elt (RootSubgroupIndex.negativeLong k) (1 : F) ∈ longRootSp2 F n k :=
    fun k => ⟨sl2Lower 1, longBlock_sl2Lower k 1⟩
  have hxcomm_pos : ∀ k : Fin n,
      x * ψc (elt (RootSubgroupIndex.positiveLong k) (1 : F)) =
        ψc (elt (RootSubgroupIndex.positiveLong k) (1 : F)) * x := by
    intro k
    have hK : (longRootSp2 F n k).map ψc ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
      rw [hfull']
      exact ⟨k, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hx _ hK) _
      (Subgroup.mem_map_of_mem ψc (hmem_pos k))).symm
  have hxcomm_neg : ∀ k : Fin n,
      x * ψc (elt (RootSubgroupIndex.negativeLong k) (1 : F)) =
        ψc (elt (RootSubgroupIndex.negativeLong k) (1 : F)) * x := by
    intro k
    have hK : (longRootSp2 F n k).map ψc ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
      rw [hfull']
      exact ⟨k, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hx _ hK) _
      (Subgroup.mem_map_of_mem ψc (hmem_neg k))).symm
  have hzmem_pos : ∀ k : Fin n, g * elt (RootSubgroupIndex.positiveLong k) (1 : F) * g⁻¹ *
      (elt (RootSubgroupIndex.positiveLong k) (1 : F))⁻¹ ∈ center (StatedSp n F) := by
    intro k
    apply hkerC
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hg, hxcomm_pos k]
    group
  have hzmem_neg : ∀ k : Fin n, g * elt (RootSubgroupIndex.negativeLong k) (1 : F) * g⁻¹ *
      (elt (RootSubgroupIndex.negativeLong k) (1 : F))⁻¹ ∈ center (StatedSp n F) := by
    intro k
    apply hkerC
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hg, hxcomm_neg k]
    group
  have hz_one_pos : ∀ k : Fin n, g * elt (RootSubgroupIndex.positiveLong k) (1 : F) * g⁻¹ *
      (elt (RootSubgroupIndex.positiveLong k) (1 : F))⁻¹ = 1 := by
    intro k
    exact eq_one_of_mem_center_of_pow_eq_one (hzmem_pos k)
      (commutator_pow_eq_one_of_commute
        (Subgroup.mem_center_iff.mp (hzmem_pos k)
          (elt (RootSubgroupIndex.positiveLong k) (1 : F))).symm (elt_one_pow_char _))
  have hz_one_neg : ∀ k : Fin n, g * elt (RootSubgroupIndex.negativeLong k) (1 : F) * g⁻¹ *
      (elt (RootSubgroupIndex.negativeLong k) (1 : F))⁻¹ = 1 := by
    intro k
    exact eq_one_of_mem_center_of_pow_eq_one (hzmem_neg k)
      (commutator_pow_eq_one_of_commute
        (Subgroup.mem_center_iff.mp (hzmem_neg k)
          (elt (RootSubgroupIndex.negativeLong k) (1 : F))).symm (elt_one_pow_char _))
  have hgcomm_pos : ∀ k : Fin n,
      Commute g (elt (RootSubgroupIndex.positiveLong k) (1 : F)) := by
    intro k
    have h1 : g * elt (RootSubgroupIndex.positiveLong k) (1 : F) * g⁻¹ =
        elt (RootSubgroupIndex.positiveLong k) (1 : F) :=
      mul_inv_eq_one.mp (hz_one_pos k)
    calc g * elt (RootSubgroupIndex.positiveLong k) (1 : F)
        = (g * elt (RootSubgroupIndex.positiveLong k) (1 : F) * g⁻¹) * g := by group
      _ = elt (RootSubgroupIndex.positiveLong k) (1 : F) * g := by rw [h1]
  have hgcomm_neg : ∀ k : Fin n,
      Commute g (elt (RootSubgroupIndex.negativeLong k) (1 : F)) := by
    intro k
    have h1 : g * elt (RootSubgroupIndex.negativeLong k) (1 : F) * g⁻¹ =
        elt (RootSubgroupIndex.negativeLong k) (1 : F) :=
      mul_inv_eq_one.mp (hz_one_neg k)
    calc g * elt (RootSubgroupIndex.negativeLong k) (1 : F)
        = (g * elt (RootSubgroupIndex.negativeLong k) (1 : F) * g⁻¹) * g := by group
      _ = elt (RootSubgroupIndex.negativeLong k) (1 : F) * g := by rw [h1]
  have hgdiag : (mat n F g).IsDiag := isDiag_of_forall_commute_root_psp hgcomm_pos hgcomm_neg
  have hgdet : (mat n F g).det ≠ 0 := by
    intro h0
    have h1 : (mat n F g).det * (mat n F g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hgpow : g ^ (Nat.card F - 1) = 1 := by
    obtain hmat := pow_card_sub_one_eq_one_of_isDiag (M := mat n F g) hgdiag hgdet
    rw [← Nat.card_eq_fintype_card] at hmat
    exact mat_injective (by rw [map_pow, map_one, hmat])
  have hcard : Nat.card F = p ^ f := GaloisField.card p f (by have := hadm.2.1; omega)
  rw [← hcard, ← hg, ← map_pow, hgpow, map_one]

end PSpProof

section POmegaOddProof

open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem eq_one_of_forall_funSet_pOmegaOdd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p f) (hX : LieModel X .POmegaOdd n p f)
    (P : Sylow 2 X) {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ p ^ f * ((p ^ f) ^ 2 - 1)) {x : X} (hxr : x ^ (r ^ a) = 1)
    (hx : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), x ∈ centralizer (K : Set X)) :
    x = 1 := by
  classical
  let F := GaloisField p f
  let θ := spinAction (quadOdd n F)
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hθker : θ.ker = center (spinGroup (quadOdd n F)) :=
    (CFSG.ComponentClassification.HarrisLit.T1.center_spinGroup_quadOdd_eq_ker h2 hn3).symm
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .POmegaOdd n p f hadm.1 hp2 (by trivial) hadm X hX
  let ψ : spinGroup (quadOdd n F) →* X := ψ₀
  have hψ : Function.Surjective ψ := hψ₀
  have hker : ψ.ker ≤ center (spinGroup (quadOdd n F)) := hker₀
  obtain ⟨R, c, hRdec, hfull⟩ :=
    exists_full_paired_frame_funSet_pOmegaOdd hp2 hadm hX ψ hψ hker P
  let ψc : spinGroup (quadOdd n F) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (spinGroup (quadOdd n F)) := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hy)
  have hfull' : FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k => (R k).map ψc) := by
    simpa [F, ψc, Subgroup.map_map] using hfull
  have hA : ∀ k, IsFundamentalOver (p ^ f) ((R k).map ψc) := fun k =>
    ⟨.POmegaOdd, n, p, f, hadm.1, hp2, rfl, trivial, hadm, ψc, hψc, hkerC, R k,
      (hRdec k).1, rfl⟩
  let k₀ : Fin (n / 2) × Bool := (⟨0, by omega⟩, false)
  obtain ⟨hZ, _, _, _⟩ :=
    fundamental_ambient_of_lieModel hadm.1 hp2 hadm hX (by simp) (hA k₀)
  have hθψ : θ.ker ≤ ψc.ker := by
    rw [hθker]
    exact ψc.center_le_ker hψc hZ
  have hψθ : ψc.ker ≤ θ.ker := hkerC.trans hθker.ge
  obtain ⟨g, rfl⟩ := hψc x
  have hgpow : g ^ (r ^ a) ∈ ψc.ker := by
    rw [MonoidHom.mem_ker, map_pow, hxr]
  have hθpow : (θ g) ^ (r ^ a) = 1 := by
    have h1 : θ (g ^ (r ^ a)) = 1 := MonoidHom.mem_ker.mp (hψθ hgpow)
    rwa [map_pow] at h1
  have hhO : θ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction (quadOdd n F) g)
  have hcommθ : ∀ (k : Fin (n / 2) × Bool) (u : spinGroup (quadOdd n F)), u ∈ R k →
      Commute (θ g) (θ u) := by
    intro k u hu
    have hxK : ψc g ∈ centralizer ((R k).map ψc : Set X) :=
      hx _ (by rw [hfull']; exact Set.mem_range_self k)
    have hcu : Commute (ψc g) (ψc u) :=
      (Subgroup.mem_centralizer_iff.mp hxK _ (Subgroup.mem_map_of_mem ψc hu)).symm
    exact commute_map_of_commute_map_of_ker_le hψθ hcu
  have hL : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      θ g * (oddOrthogonalPairFrame F n j).La A = (oddOrthogonalPairFrame F n j).La A * θ g := by
    intro j A
    have hmem : (oddOrthogonalPairFrame F n j).La A ∈ (R (j, false)).map θ := by
      rw [(hRdec (j, false)).2]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, false) u hu
  have hR : ∀ (j : Fin (n / 2)) (A : SL(2, F)),
      θ g * (oddOrthogonalPairFrame F n j).swap.La A =
        (oddOrthogonalPairFrame F n j).swap.La A * θ g := by
    intro j A
    have hmem : (oddOrthogonalPairFrame F n j).swap.La A ∈ (R (j, true)).map θ := by
      rw [(hRdec (j, true)).2]
      exact ⟨A, rfl⟩
    obtain ⟨u, hu, hAu⟩ := Subgroup.mem_map.mp hmem
    rw [← hAu]
    exact hcommθ (j, true) u hu
  have hcard : Nat.card F = p ^ f :=
    GaloisField.card p f (by have := hadm.2.1; omega)
  have hrq' : ¬ r ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hcard]
    exact hrq
  have hθ1 : θ g = 1 := eq_one_of_commute_oddPairFrames h2 hr hr2 hrq' hhO hθpow hL hR
  have hgker : g ∈ θ.ker := MonoidHom.mem_ker.mpr hθ1
  exact MonoidHom.mem_ker.mp (hθψ hgker)

end POmegaOddProof

theorem eq_bot_of_forall_funSet_psp_or_psl
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : StatedLieTag} {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible t n p 1) (ht : FunManyType t n)
    (hX : LieModel X t n p 1) (hrow : t = .PSp ∨ t = .PSL) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hpow : ∀ x ∈ B, x ^ (p ^ 1 - 1) = 1 := by
    intro x hx
    have hx' : ∀ K ∈ FunSet (fundPred (p ^ 1)) X (P : Subgroup X),
        x ∈ centralizer (K : Set X) := by
      intro K hK
      rw [pow_one] at hK
      exact hcent K hK hx
    rcases hrow with rfl | rfl
    · exact pow_sub_one_eq_one_of_forall_funSet_psp hp2 hadm hX P hx'
    · have h6 : 6 ≤ n := ht
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
      · obtain ⟨m, hm⟩ : ∃ m, 2 * k = 2 * m + 1 + 1 := ⟨k - 1, by omega⟩
        rw [hm] at hadm hX
        exact pow_sub_one_eq_one_of_forall_funSet_psl_even hp2 (by omega) hadm hX P hx'
      · obtain ⟨m, hm⟩ : ∃ m, 2 * k + 1 = 2 * m + 1 + 1 + 1 := ⟨k - 1, by omega⟩
        rw [hm] at hadm hX
        exact pow_sub_one_eq_one_of_forall_funSet_psl_odd hp2 (by omega) hadm hX P hx'
  refine eq_bot_of_isPGroup_of_forall_pow_eq_one hB
    ((Nat.Prime.coprime_iff_not_dvd hr).2 fun hd => ?_) hpow
  have := Nat.le_of_dvd (by rcases hp35 with rfl | rfl <;> norm_num) hd
  rcases hp35 with rfl | rfl <;> omega

theorem eq_bot_of_forall_funSet_psu
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible .PSU n p 1) (ht : FunManyType .PSU n)
    (hX : LieModel X .PSU n p 1) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hpow : ∀ x ∈ B, x ^ ((p ^ 1) ^ 2 - 1) = 1 := by
    intro x hx
    have hx' : ∀ K ∈ FunSet (fundPred (p ^ 1)) X (P : Subgroup X),
        x ∈ centralizer (K : Set X) := by
      intro K hK
      rw [pow_one] at hK
      exact hcent K hK hx
    have h6 : 6 ≤ n := ht
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · obtain ⟨m, hm⟩ : ∃ m, 2 * k = 2 * m + 1 + 1 := ⟨k - 1, by omega⟩
      rw [hm] at hadm hX
      exact pow_sq_sub_one_eq_one_of_forall_funSet_psu_even hp2 (by omega) hadm hX P hx'
    · obtain ⟨m, hm⟩ : ∃ m, 2 * k + 1 = 2 * m + 1 + 1 + 1 := ⟨k - 1, by omega⟩
      rw [hm] at hadm hX
      exact pow_sq_sub_one_eq_one_of_forall_funSet_psu_odd hp2 (by omega) hadm hX P hx'
  refine eq_bot_of_isPGroup_of_forall_pow_eq_one hB
    ((Nat.Prime.coprime_iff_not_dvd hr).2 fun hd => ?_) hpow
  have hle : r ≤ 24 := by
    have := Nat.le_of_dvd (by rcases hp35 with rfl | rfl <;> norm_num) hd
    rcases hp35 with rfl | rfl <;> norm_num at this <;> omega
  rcases hp35 with rfl | rfl <;> interval_cases r <;> (revert hd hr; norm_num)

theorem eq_bot_of_forall_funSet_pOmegaOdd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible .POmegaOdd n p 1)
    (hX : LieModel X .POmegaOdd n p 1) (P : Sylow 2 X) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ FunSet (fundPred p) X (P : Subgroup X), B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hrq : ¬ r ∣ p ^ 1 * ((p ^ 1) ^ 2 - 1) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (by simpa using hd))
    · have hle : r ≤ 24 := by
        have := Nat.le_of_dvd (by rcases hp35 with rfl | rfl <;> norm_num) hd
        rcases hp35 with rfl | rfl <;> norm_num at this <;> omega
      rcases hp35 with rfl | rfl <;> interval_cases r <;> (revert hd hr; norm_num)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hB ⟨x, hx⟩
  have hxr : x ^ (r ^ a) = 1 := by simpa using congrArg Subtype.val ha
  refine Subgroup.mem_bot.2 (eq_one_of_forall_funSet_pOmegaOdd hp2 hadm hX P hr (by omega) hrq
    hxr fun K hK => ?_)
  rw [pow_one] at hK
  exact hcent K hK hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
