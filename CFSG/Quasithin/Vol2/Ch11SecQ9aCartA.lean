module

public import CFSG.Quasithin.Vol2.KGNatSL3Row

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.Quasithin.Vol2.KGNat
open scoped MatrixGroups

variable (K : Type) [Field K]

@[expose] noncomputable def rad1 : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (leviHom K).ker.map (stabE0 K).subtype

@[expose] noncomputable def rad2 : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (leviHom2 K).ker.map (stabRow2 K).subtype

variable {K}

theorem mem_rad1 {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ rad1 K ↔ B ∈ stabE0 K ∧ lev (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
  constructor
  · rintro ⟨⟨B, hB⟩, hk, rfl⟩
    refine ⟨hB, ?_⟩
    have h2 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
      (MonoidHom.mem_ker.mp hk)
    simpa [leviHom_coe] using h2
  · rintro ⟨hB, hl⟩
    refine ⟨⟨B, hB⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [leviHom_coe, Matrix.SpecialLinearGroup.coe_one]
    exact hl

theorem mem_rad2 {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ rad2 K ↔ B ∈ stabRow2 K ∧ lev2 (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
  constructor
  · rintro ⟨⟨B, hB⟩, hk, rfl⟩
    refine ⟨hB, ?_⟩
    have h2 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
      (MonoidHom.mem_ker.mp hk)
    simpa [leviHom2_coe] using h2
  · rintro ⟨hB, hl⟩
    refine ⟨⟨B, hB⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [leviHom2_coe, Matrix.SpecialLinearGroup.coe_one]
    exact hl

theorem rad1_entries {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ rad1 K) :
    (B : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧ (B : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  obtain ⟨hs, hl⟩ := mem_rad1.mp hB
  obtain ⟨h00, h10, h20⟩ := stabE0_entries hs
  have h11 := congrFun (congrFun hl 0) 0
  have h12 := congrFun (congrFun hl 0) 1
  have h21 := congrFun (congrFun hl 1) 0
  have h22 := congrFun (congrFun hl 1) 1
  simp only [lev_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h11 h12 h21 h22
  exact ⟨h00, h10, h20, h11, h12, h21, h22⟩

theorem rad2_entries {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ rad2 K) :
    (B : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧ (B : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  obtain ⟨hs, hl⟩ := mem_rad2.mp hB
  obtain ⟨h20, h21, h22⟩ := mem_stabRow2.mp hs
  have h00 := congrFun (congrFun hl 0) 0
  have h01 := congrFun (congrFun hl 0) 1
  have h10 := congrFun (congrFun hl 1) 0
  have h11 := congrFun (congrFun hl 1) 1
  simp only [lev2_apply, Fin.castSucc_zero, Fin.castSucc_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11, h20, h21, h22⟩

theorem mem_rad1_iff_uSL {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ rad1 K ↔ ∃ a b : K,
      B = CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL a b 0 := by
  constructor
  · intro hB
    obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := rad1_entries hB
    refine ⟨(B : Matrix (Fin 3) (Fin 3) K) 0 1, (B : Matrix (Fin 3) (Fin 3) K) 0 2,
      Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, h00, h10, h20, h11, h12, h21, h22]
  · rintro ⟨a, b, rfl⟩
    refine mem_rad1.mpr ⟨mem_stabE0.mpr ?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
          CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lev, CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
          CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat]

theorem mem_rad2_iff_uSL {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ rad2 K ↔ ∃ b c : K,
      B = CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL 0 b c := by
  constructor
  · intro hB
    obtain ⟨h00, h01, h10, h11, h20, h21, h22⟩ := rad2_entries hB
    refine ⟨(B : Matrix (Fin 3) (Fin 3) K) 0 2, (B : Matrix (Fin 3) (Fin 3) K) 1 2,
      Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, h00, h01, h10, h11, h20, h21, h22]
  · rintro ⟨b, c, rfl⟩
    refine mem_rad2.mpr ⟨mem_stabRow2.mpr ⟨rfl, rfl, rfl⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lev2, CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat]

variable [CharP K 2]

theorem sq_eq_one_of_mem_rad1 {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ rad1 K) :
    B ^ 2 = 1 := by
  obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := rad1_entries hB
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, h11, h12, h21, h22] <;>
    first
      | linear_combination (B : Matrix (Fin 3) (Fin 3) K) 0 1 * h2
      | linear_combination (B : Matrix (Fin 3) (Fin 3) K) 0 2 * h2

theorem sq_eq_one_of_mem_rad2 {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ rad2 K) :
    B ^ 2 = 1 := by
  obtain ⟨h00, h01, h10, h11, h20, h21, h22⟩ := rad2_entries hB
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22] <;>
    first
      | linear_combination (B : Matrix (Fin 3) (Fin 3) K) 0 2 * h2
      | linear_combination (B : Matrix (Fin 3) (Fin 3) K) 1 2 * h2

variable [Finite K]

theorem pCoreOf_stabE0 : pCoreOf 2 (stabE0 K) = rad1 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pCoreOf rad1
  congr 1
  apply le_antisymm
  · have : ((CFSG.Open.pCore 2 ↥(stabE0 K)).map (leviHom K)).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map _ leviHom_surjective
    have h := eq_bot_of_normal_isPGroup_SL2
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(stabE0 K))).map (leviHom K))
    rwa [Subgroup.map_eq_bot_iff] at h
  · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun x => ⟨1, ?_⟩
    have hx : ((x : ↥(stabE0 K)) : SpecialLinearGroup (Fin 3) K) ∈ rad1 K :=
      ⟨x, x.2, rfl⟩
    refine Subtype.ext (Subtype.ext ?_)
    simpa using sq_eq_one_of_mem_rad1 hx

theorem pCoreOf_stabRow2 : pCoreOf 2 (stabRow2 K) = rad2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pCoreOf rad2
  congr 1
  apply le_antisymm
  · have : ((CFSG.Open.pCore 2 ↥(stabRow2 K)).map (leviHom2 K)).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map _ leviHom2_surjective
    have h := eq_bot_of_normal_isPGroup_SL2
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(stabRow2 K))).map (leviHom2 K))
    rwa [Subgroup.map_eq_bot_iff] at h
  · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun x => ⟨1, ?_⟩
    have hx : ((x : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K) ∈ rad2 K :=
      ⟨x, x.2, rfl⟩
    refine Subtype.ext (Subtype.ext ?_)
    simpa using sq_eq_one_of_mem_rad2 hx

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
