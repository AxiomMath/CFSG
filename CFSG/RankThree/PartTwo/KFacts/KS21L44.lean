module

public import CFSG.RankThree.PartTwo.KFacts.KS21TwoCentral
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.L44

open Matrix CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial

abbrev F4 := GaloisField 2 2

abbrev M := SpecialLinearGroup (Fin 4) F4

theorem card_F4 : Nat.card F4 = 4 := GaloisField.card 2 2 (by norm_num)

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  classical
  have := Fintype.ofFinite F4
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, card_F4]

theorem units_pow_three (μ : F4ˣ) : μ ^ 3 = 1 := by
  rw [← card_units_F4]
  exact pow_card_eq_one'

theorem two_eq_zero : (2 : F4) = 0 := CharTwo.two_eq_zero

theorem center_M : Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 :=
    CFSG.LieType.BorelTits.eq_one_of_pow_char_pow_eq_one 2 (e := 2) (by norm_num [hr])
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

@[expose] def equivSL : projSL 4 F4 ≃* M :=
  (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL 4 F4)).symm.trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSL 4 F4)).symm.trans
      ((projectiveSpecialLinearGroupEquivStatedProj 4 F4).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq center_M).trans QuotientGroup.quotientBot)))

theorem eq_one_add_single_of_mem_center {u : M} (hu : u ∈ LinearFlag.unitriangular 4 F4)
    (hc : ∀ v ∈ LinearFlag.unitriangular 4 F4, u * v = v * u) :
    ∃ b : F4, (u : Matrix (Fin 4) (Fin 4) F4) = 1 + single 0 3 b := by
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := 4)
    (by norm_num) (u : Matrix (Fin 4) (Fin 4) F4) (by
      intro i j hij
      have hlt : i < j := by
        rw [Fin.lt_def]
        omega
      have h := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4))
        (hc _ (CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hlt (1 : F4)))
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        mul_add, add_mul, mul_one, one_mul] at h
      exact add_left_cancel h)
  have ha : a = 1 := by
    have h00 := congrFun₂ hab 0 0
    rw [(LinearFlag.mem_unitriangular.mp hu).2 0] at h00
    simpa [single_apply] using h00.symm
  refine ⟨b, ?_⟩
  rw [hab, ha, one_smul, smul_single, smul_eq_mul, mul_one]
  rfl

theorem det_diag (μ ν : F4ˣ) :
    (diagonal ![((μ * ν : F4ˣ) : F4), (μ : F4), (ν : F4), ((μ * ν : F4ˣ) : F4)]).det = 1 := by
  have h1 := congrArg Units.val (units_pow_three μ)
  have h2 := congrArg Units.val (units_pow_three ν)
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h1 h2
  rw [det_diagonal, Fin.prod_univ_four]
  simp only [Units.val_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  linear_combination (ν : F4) ^ 3 * h1 + h2

@[expose] def diagHom : F4ˣ × F4ˣ →* M where
  toFun x := ⟨diagonal ![((x.1 * x.2 : F4ˣ) : F4), (x.1 : F4), (x.2 : F4),
    ((x.1 * x.2 : F4ˣ) : F4)], det_diag x.1 x.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring

theorem coe_diagHom (x : F4ˣ × F4ˣ) :
    ((diagHom x : M) : Matrix (Fin 4) (Fin 4) F4) =
      diagonal ![((x.1 * x.2 : F4ˣ) : F4), (x.1 : F4), (x.2 : F4), ((x.1 * x.2 : F4ˣ) : F4)] :=
  rfl

theorem diagHom_injective : Function.Injective diagHom := by
  intro x y h
  have h' := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h
  simp only [coe_diagHom] at h'
  have h1 := congrFun₂ h' 1 1
  have h2 := congrFun₂ h' 2 2
  simp at h1 h2
  exact Prod.ext (Units.ext h1) (Units.ext h2)

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 0, 0, 0; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; 0, 0, 0, 1]

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) F4) :
    blockMat (A * B) = blockMat A * blockMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem det_blockMat (A : Matrix (Fin 2) (Fin 2) F4) : (blockMat A).det = A.det := by
  rw [Matrix.det_fin_two, det_succ_row_zero, Fin.sum_univ_four]
  simp [blockMat, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix]

@[expose] def blockHom : SpecialLinearGroup (Fin 2) F4 →* M where
  toFun A := ⟨blockMat (A : Matrix (Fin 2) (Fin 2) F4), by rw [det_blockMat]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat]
  map_mul' A B := by
    apply Subtype.ext
    exact blockMat_mul _ _

theorem coe_blockHom (A : SpecialLinearGroup (Fin 2) F4) :
    ((blockHom A : M) : Matrix (Fin 4) (Fin 4) F4) = blockMat (A : Matrix (Fin 2) (Fin 2) F4) :=
  rfl

theorem blockHom_injective : Function.Injective blockHom := by
  intro A B h
  have h' := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h
  simp only [coe_blockHom] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blockMat] using congrFun₂ h' 1 1
  · simpa [blockMat] using congrFun₂ h' 1 2
  · simpa [blockMat] using congrFun₂ h' 2 1
  · simpa [blockMat] using congrFun₂ h' 2 2

theorem isSimpleGroup_SL2 : IsSimpleGroup (SpecialLinearGroup (Fin 2) F4) := by
  have := Fintype.ofFinite F4
  have h4 : ∃ s : Finset F4, s.card = 4 := ⟨Finset.univ, by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_F4]⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F4)).symm.isSimpleGroup

theorem card_SL2 : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 := by
  rw [LinearFlag.card_SL_eq (by norm_num), card_F4]
  decide

theorem isGoodInvolution_of_coe {z : M} {b : F4} (hb : b ≠ 0)
    (hz : (z : Matrix (Fin 4) (Fin 4) F4) = 1 + single 0 3 b) : IsGoodInvolution z := by
  have hcomm_diag : ∀ x, diagHom x * z = z * diagHom x := by
    intro x
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagHom, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, single_apply, diagonal_apply, mul_comm]
  have hcomm_block : ∀ A, blockHom A * z = z * blockHom A := by
    intro A
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockHom, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, single_apply,
      blockMat]
  have hC : ∀ g : M, g * z = z * g → g ∈ Subgroup.centralizer ({z} : Set M) := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg
  refine ⟨?_, ?_, blockHom.range, ?_, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · apply Subtype.ext
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, single_apply, two_eq_zero, ← two_mul]
    · intro h
      have := congrFun₂ (congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h) 0 3
      simp [hz] at this
      exact hb this
  · apply CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
      (fun a => Prod.ext (units_pow_three _) (units_pow_three _))
      (by rw [Nat.card_prod, card_units_F4]; norm_num) diagHom diagHom_injective
    rintro _ ⟨x, rfl⟩
    exact hC _ (hcomm_diag x)
  · rintro _ ⟨A, rfl⟩
    exact hC _ (hcomm_block A)
  · have := isSimpleGroup_SL2
    exact (MonoidHom.ofInjective blockHom_injective).symm.isSimpleGroup
  · rw [← Nat.card_congr (MonoidHom.ofInjective blockHom_injective).toEquiv, card_SL2]
    norm_num
  · rw [← Nat.card_congr (MonoidHom.ofInjective blockHom_injective).toEquiv, card_SL2]
    norm_num

theorem isGoodInvolution_of_sylow (S : Sylow 2 M) (z : M) (hzS : z ∈ (S : Subgroup M))
    (hzC : z ∈ Subgroup.centralizer ((S : Subgroup M) : Set M)) (hz2 : orderOf z = 2) :
    IsGoodInvolution z := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := F4) 2 (n := 4) (by norm_num)
  refine forall_good_of_sylow P (fun u huP huC hu2 => ?_) S z hzS hzC hz2
  rw [hP] at huP huC
  obtain ⟨b, hb⟩ := eq_one_add_single_of_mem_center huP (fun v hv =>
    ((Subgroup.mem_centralizer_iff.mp huC) v hv).symm)
  refine isGoodInvolution_of_coe (fun h0 => ?_) hb
  rw [h0, single_zero, add_zero] at hb
  have : u = 1 := Subtype.ext hb
  rw [this, orderOf_one] at hu2
  omega

theorem two_dvd_card_M : 2 ∣ Nat.card M := by
  rw [LinearFlag.card_SL_eq (by norm_num), card_F4]
  decide

instance : Finite (projSL 4 F4) := Finite.of_equiv M equivSL.symm.toEquiv

theorem hasLongRootSet_projSL : HasLongRootSet (projSL 4 F4) :=
  (hasLongRootSet_of_forall two_dvd_card_M isGoodInvolution_of_sylow).of_mulEquiv equivSL.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.L44
