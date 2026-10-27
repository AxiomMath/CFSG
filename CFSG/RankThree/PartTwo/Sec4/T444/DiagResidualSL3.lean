module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualE9
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualGen
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.ResidualGen

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.RankThree.PartTwo.KFacts.L34
open Matrix

section Matrices

variable {F : Type} [Field F]

theorem proj_eq_proj_of_smul {x y : SpecialLinearGroup (Fin 3) F} {c : F} (hc : c ^ 3 = 1)
    (h : (y : Matrix (Fin 3) (Fin 3) F) = c • (x : Matrix (Fin 3) (Fin 3) F)) :
    proj 3 F x = proj 3 F y := by
  rw [proj_eq_proj_iff]
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine mem_scalars.mpr ⟨Units.mk0 c hc0, by ext; simpa using hc, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_mul, x.2, one_smul, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]

end Matrices

section Elements

variable {F : Type} [Field F] [CharP F 2] {ω : F} (hω : ω * ω + ω + 1 = 0)
include hω

theorem omega_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

theorem det_hM : (LinearFieldFour.hM ω).det = 1 := by
  simp only [LinearFieldFour.hM, det_fin_three]
  simp
  linear_combination omega_cube hω

theorem det_hiM : (hiM ω).det = 1 := by
  simp only [hiM, det_fin_three]
  simp
  linear_combination omega_cube hω

@[expose] def hS : SpecialLinearGroup (Fin 3) F := ⟨LinearFieldFour.hM ω, det_hM hω⟩

@[expose] def hiS : SpecialLinearGroup (Fin 3) F := ⟨hiM ω, det_hiM hω⟩

@[expose] def fS : SpecialLinearGroup (Fin 3) F := ⟨fM ω, det_fM hω⟩

@[expose] def jS : SpecialLinearGroup (Fin 3) F := ⟨jM ω, det_jM hω⟩

theorem coe_hS : ((hS hω : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    LinearFieldFour.hM ω := rfl

theorem coe_hiS : ((hiS hω : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hiM ω :=
  rfl

theorem coe_fS : ((fS hω : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = fM ω := rfl

theorem coe_jS : ((jS hω : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = jM ω := rfl

omit hω in
theorem coe_rS : ((rSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = rM :=
  coe_rSL

theorem hS_pow_three : hS hω ^ 3 = (1 : SpecialLinearGroup (Fin 3) F) := by
  have h3 := omega_cube hω
  apply Subtype.ext
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_hS, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.hM, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination h3
  · linear_combination (ω ^ 3 + 1) * h3

omit hω in
theorem rSL_pow_three : (rSL : SpecialLinearGroup (Fin 3) F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_rS, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rM, Matrix.mul_apply, Fin.sum_univ_three]

theorem fM_sq : fM ω * fM ω = !![0, 1, 0; ω * ω, 0, 0; 0, 0, ω] := by
  simp only [fM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem fM_pow_four : fM ω * fM ω * (fM ω * fM ω) = (ω * ω) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [fM_sq hω]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply]

end Elements

section Relations

variable {F : Type} [Field F] [CharP F 2] {ω : F} (hω : ω * ω + ω + 1 = 0)
include hω

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero (1 : F)
  have : (1 : F) = 0 := by linear_combination hω - h2
  exact one_ne_zero this

theorem hS_mul_hiS : hS hω * hiS hω = (1 : SpecialLinearGroup (Fin 3) F) :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_hS, coe_hiS, hM_mul_hiM hω,
      Matrix.SpecialLinearGroup.coe_one])

theorem proj_hS_inv : (proj 3 F (hS hω))⁻¹ = proj 3 F (hiS hω) :=
  inv_eq_of_mul_eq_one_right (by rw [← map_mul, hS_mul_hiS hω, map_one])

theorem rel_comm : proj 3 F (hS hω) * proj 3 F rSL = proj 3 F rSL * proj 3 F (hS hω) := by
  rw [← map_mul, ← map_mul]
  refine proj_eq_proj_of_smul (c := ω) (omega_cube hω) ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_hS, coe_rS]
  exact rM_mul_hM hω

theorem rel_fa : proj 3 F (fS hω) * proj 3 F (hS hω) = proj 3 F rSL * proj 3 F (fS hω) := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_hS, coe_fS, coe_rS]
  exact fM_mul_hM hω

theorem rel_fb : proj 3 F (fS hω) * proj 3 F rSL = proj 3 F (hiS hω) * proj 3 F (fS hω) := by
  rw [← map_mul, ← map_mul]
  refine (proj_eq_proj_of_smul (c := ω) (omega_cube hω) ?_).symm
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_fS, coe_rS,
    coe_hiS, ← Matrix.smul_mul]
  exact fM_mul_rM hω

theorem rel_f4 : proj 3 F (fS hω) ^ 4 = 1 := by
  rw [← map_pow, ← map_one (proj 3 F)]
  refine (proj_eq_proj_of_smul (c := ω * ω) ?_ ?_).symm
  · have := omega_cube hω
    calc (ω * ω) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [this, one_pow]
  · rw [Matrix.SpecialLinearGroup.coe_pow, coe_fS, show (4 : ℕ) = 2 + 2 by norm_num, pow_add, sq,
      fM_pow_four hω, Matrix.SpecialLinearGroup.coe_one]

theorem rel_ja : proj 3 F (jS hω) * proj 3 F (hS hω) =
    proj 3 F rSL * proj 3 F (hiS hω) * proj 3 F (jS hω) := by
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_jS, coe_hS, coe_rS, coe_hiS]
  exact jM_mul_hM hω

theorem rel_jb : proj 3 F (jS hω) * proj 3 F rSL =
    proj 3 F (hiS hω) * proj 3 F rSL * proj 3 F (hiS hω) * proj 3 F (jS hω) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  refine (proj_eq_proj_of_smul (c := ω) (omega_cube hω) ?_).symm
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_jS, coe_rS, coe_hiS,
    ← Matrix.smul_mul]
  exact jM_mul_rM hω

end Relations

section Data

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem proj_rSL_ne_proj_of_zero {X : SpecialLinearGroup (Fin 3) F}
    (hX : (X : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) : proj 3 F rSL ≠ proj 3 F X := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have h1 : (X : Matrix (Fin 3) (Fin 3) F) =
      ((rSL : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (c : F) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h2 := congrFun (congrFun h1 0) 2
  rw [hX, coe_rSL] at h2
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at h2
  exact c.ne_zero h2.symm

variable {ω : F} (hω : ω * ω + ω + 1 = 0)
include hω

theorem proj_hS_ne_one : proj 3 F (hS hω) ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  simp [coe_hS, LinearFieldFour.hM, scalar_apply] at h0 h1
  exact omega_ne_one hω (h0.trans h1.symm)

theorem proj_rSL_not_mem_zpowers :
    proj 3 F rSL ∉ Subgroup.zpowers (proj 3 F (hS hω)) := by
  rintro ⟨i, hi⟩
  have ha3 : proj 3 F (hS hω) ^ 3 = 1 := by rw [← map_pow, hS_pow_three hω, map_one]
  obtain ⟨n, hn3, hn⟩ : ∃ n : ℕ, n < 3 ∧ proj 3 F (hS hω) ^ i = proj 3 F (hS hω) ^ n := by
    have h3 : proj 3 F (hS hω) ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    refine ⟨(i % 3).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_eq_zpow_emod i h3]
  have hi' : proj 3 F (hS hω) ^ i = proj 3 F rSL := hi
  rw [hn] at hi'
  interval_cases n
  · exact proj_rSL_ne_proj_of_zero (F := F) (X := 1) (by simp) (by rw [map_one]; simpa using hi'.symm)
  · exact proj_rSL_ne_proj_of_zero (X := hS hω) (by simp [coe_hS, LinearFieldFour.hM])
      (by simpa using hi'.symm)
  · have h2 : proj 3 F (hS hω) ^ 2 = proj 3 F (hiS hω) := by
      rw [← proj_hS_inv hω]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha3)
    exact proj_rSL_ne_proj_of_zero (X := hiS hω) (by simp [coe_hiS, hiM]) (by rw [← h2]; exact hi'.symm)

theorem exists_e9_projectiveSL [Finite F] :
    ∃ E : Subgroup (projectiveSL 3 F), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 ∧
      (∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer (E : Set (projectiveSL 3 F)), n * x * n⁻¹ = y) ∧
      ∃ s : projectiveSL 3 F, s * s = 1 ∧ ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  have hfa : proj 3 F (fS hω) * proj 3 F (hS hω) * (proj 3 F (fS hω))⁻¹ = proj 3 F rSL := by
    rw [rel_fa hω, mul_assoc, mul_inv_cancel, mul_one]
  have hfb : proj 3 F (fS hω) * proj 3 F rSL * (proj 3 F (fS hω))⁻¹ =
      (proj 3 F (hS hω))⁻¹ := by
    rw [rel_fb hω, proj_hS_inv hω, mul_assoc, mul_inv_cancel, mul_one]
  have hja : proj 3 F (jS hω) * proj 3 F (hS hω) * (proj 3 F (jS hω))⁻¹ =
      proj 3 F rSL * (proj 3 F (hS hω))⁻¹ := by
    rw [rel_ja hω, proj_hS_inv hω, mul_assoc, mul_inv_cancel, mul_one]
  have hjb : proj 3 F (jS hω) * proj 3 F rSL * (proj 3 F (jS hω))⁻¹ =
      (proj 3 F (hS hω))⁻¹ * proj 3 F rSL * (proj 3 F (hS hω))⁻¹ := by
    rw [rel_jb hω, proj_hS_inv hω, mul_assoc, mul_inv_cancel, mul_one]
  exact exists_e9_data (by rw [← map_pow, hS_pow_three hω, map_one])
    (by rw [← map_pow, rSL_pow_three, map_one]) (rel_comm hω) (proj_hS_ne_one hω)
    (proj_rSL_not_mem_zpowers hω) hfa hfb (rel_f4 hω) hja hjb

end Data

section Final

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sq_eq_one_of_mem_projRad_zero {r : projectiveSL 3 F}
    (hr : r ∈ FieldFourCover.projRad F 0) : r ^ 2 = 1 := by
  obtain ⟨a, c, rfl⟩ := FieldFourCover.mem_projRad_zero.1 hr
  rw [← map_pow, sq, FieldFourCover.unipU_mul]
  simp only [CharTwo.add_self_eq_zero, mul_zero, FieldFourCover.unipU_zero, map_one]

theorem isSimpleGroup_projectiveSL_three : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 _)).isSimpleGroup

theorem card_projectiveSL_three_big (hq : 4 ≤ Nat.card F) : 5040 < Nat.card (projectiveSL 3 F) := by
  have h := CFSG.RankThree.PartTwo.KFacts.card_projectiveSL_mul_card_scalars (K := F) (n := 3)
    (by norm_num)
  have hsc : Nat.card (scalars 3 F) ≤ 3 := by
    rw [card_scalars_eq_gcd F (by norm_num)]
    exact Nat.gcd_le_left _ (by norm_num)
  have hrhs : Nat.card F ^ (3 * (3 - 1) / 2) * ∏ j ∈ Finset.Icc 2 3, (Nat.card F ^ j - 1) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  rw [hrhs] at h
  by_contra hle
  push Not at hle
  have h1 : 4 ^ 3 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 4 ^ 2 - 1 ≤ Nat.card F ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : 4 ^ 3 - 1 ≤ Nat.card F ^ 3 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) ≤ 5040 * 3 :=
    Nat.mul_le_mul hle hsc
  have h5 : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  norm_num at h5
  omega

theorem residualData_projectiveSL (hq : 4 ≤ Nat.card F) (h3 : 3 ∣ Nat.card F - 1) :
    ResidualData (projectiveSL 3 F) := by
  obtain ⟨ω, hprim⟩ := Sec19.Item19Res5Proof.exists_isPrimitiveRoot_three h3
  have hω : ω * ω + ω + 1 = 0 := by
    have := hprim.geom_sum_eq_zero (by norm_num : 1 < 3)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  haveI : IsSimpleGroup (projectiveSL 3 F) := isSimpleGroup_projectiveSL_three
  refine ⟨isSimpleGroup_projectiveSL_three, ?_, card_projectiveSL_three_big hq, ?_,
    exists_e9_projectiveSL hω⟩
  · refine ⟨proj 3 F (fS hω), proj 3 F (hS hω), fun h => ?_⟩
    have h2 := rel_fa hω
    rw [h] at h2
    have h4 : proj 3 F (hS hω) = proj 3 F rSL := mul_right_cancel h2
    apply proj_rSL_not_mem_zpowers hω
    rw [← h4]
    exact Subgroup.mem_zpowers _
  · have hel : CFSG.Open.IsElemAbelian 2 (FieldFourCover.projRad F 0) :=
      ⟨⟨⟨fun a b => Subtype.ext (FieldFourCover.commute_of_mem_projRad 0 a.2 b.2)⟩⟩,
        fun x hx => sq_eq_one_of_mem_projRad_zero hx⟩
    obtain ⟨E, -, hE, hEc⟩ := CFSG.LieType.SeitzGeneration.exists_isElemAbelian_card_of_le (k := 4)
      Nat.prime_two hel (by rw [FieldFourCover.card_projRad]; nlinarith)
    have := hE.1
    exact ⟨E, fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩), hE.2, by
      rw [hEc]; norm_num⟩

end Final

end CFSG.RankThree.PartTwo.Sec4.ResidualGen
