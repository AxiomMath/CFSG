module

public import CFSG.Milestones.ASVolI.A3L3.Core

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

theorem burnsideA315y_isPGroup_zpowers {G : Type} [Group G] {g : G} (hg : g ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers g) := by
  intro x
  refine ⟨2, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  apply Subtype.ext
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← hk, show (2 : ℕ) ^ 2 = 4 by norm_num, ← zpow_natCast, ← _root_.zpow_mul, mul_comm k,
    _root_.zpow_mul, zpow_natCast, hg, _root_.one_zpow]

theorem burnsideA315y_isPGroup_quat {G : Type} [Group G] {a b : G} (ha : a ^ 4 = 1)
    (hb : b ^ 4 = 1) (hba : b * a * b⁻¹ = a ^ 3) :
    IsPGroup 2 ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers a) := by
  refine IsPGroup.to_sup_of_normal_right' (burnsideA315y_isPGroup_zpowers hb)
    (burnsideA315y_isPGroup_zpowers ha) ?_
  have hconj : ∀ k : ℤ, b * a ^ k * b⁻¹ = (a ^ 3) ^ k := by
    intro k
    rw [← conj_zpow, hba]
  have ha3 : (a ^ 3) ^ 3 = a := by
    rw [← pow_mul, show 3 * 3 = 4 * 2 + 1 by norm_num, pow_succ, pow_mul, ha, one_pow, one_mul]
  have h1 : b * a ^ 3 * b⁻¹ = a := by
    rw [← conj_pow, hba, ha3]
  have h1' : b⁻¹ * a * b⁻¹⁻¹ = a ^ 3 := by
    calc b⁻¹ * a * b⁻¹⁻¹ = b⁻¹ * (b * a ^ 3 * b⁻¹) * b⁻¹⁻¹ := by rw [h1]
      _ = a ^ 3 := by group
  have hconj' : ∀ k : ℤ, b⁻¹ * a ^ k * b = (a ^ 3) ^ k := by
    intro k
    calc b⁻¹ * a ^ k * b = b⁻¹ * a ^ k * b⁻¹⁻¹ := by rw [inv_inv]
      _ = (b⁻¹ * a * b⁻¹⁻¹) ^ k := conj_zpow.symm
      _ = (a ^ 3) ^ k := by rw [h1']
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [hconj k]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 3) k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : y = b⁻¹ * a ^ k * b := by rw [hk]; group
    rw [this, hconj' k]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 3) k

theorem burnsideA315y_exists_sylow_le {Γ : Type} [Group Γ] [Finite Γ] {C Q : Subgroup Γ}
    (hQ : IsPGroup 2 ↥Q) (hQC : Q ≤ C) :
    ∃ S : Subgroup Γ, Q ≤ S ∧ S ≤ C ∧ IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 ↥(Q.subgroupOf C) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  refine ⟨(P : Subgroup ↥C).map C.subtype, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨⟨q, hQC hq⟩, hP (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  · rintro _ ⟨s, -, rfl⟩
    exact s.2
  · exact P.isPGroup'.map C.subtype
  · have h1 : ((P : Subgroup ↥C).map C.subtype).subgroupOf C = (P : Subgroup ↥C) := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    show ¬ 2 ∣ (((P : Subgroup ↥C).map C.subtype).subgroupOf C).index
    rw [h1]
    exact P.not_dvd_index

theorem burnsideA315y_det_inv_eq_one {F : Type} [Field F] {Γ : Subgroup (GL (Fin 3) F)} {a : ↥Γ}
    (ha : ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1) :
    (((a⁻¹ : ↥Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (a : GL (Fin 3) F)))
  rw [Units.val_mul, Matrix.det_mul, ha, one_mul, Units.val_one, Matrix.det_one] at h
  simpa using h

@[expose] def burnsideA315y_C1 {F : Type} [Field F] (Γ : Subgroup (GL (Fin 3) F)) (zh : ↥Γ) :
    Subgroup ↥Γ where
  carrier := {g | ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ g * zh = zh * g}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, ha, hb, mul_one]
    · exact Commute.mul_left (show Commute a zh from ha') (show Commute b zh from hb')
  one_mem' := ⟨by simp, by rw [one_mul, mul_one]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨burnsideA315y_det_inv_eq_one ha, (show Commute a zh from ha').inv_left⟩

section Quat

variable {F : Type} [Field F]

theorem burnsideA315y_qa_mul_qa : burnsideA315y_qa F * burnsideA315y_qa F = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideA315y_qa, Matrix.mul_apply, Fin.sum_univ_two]

theorem burnsideA315y_det_qa : (burnsideA315y_qa F).det = 1 := by
  simp [burnsideA315y_qa, Matrix.det_fin_two]

theorem burnsideA315y_qb_mul_qb (x y cc : F) :
    (cc • burnsideA315y_qb x y) * (cc • burnsideA315y_qb x y) = (cc ^ 2 * (x ^ 2 + y ^ 2)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315y_qb, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem burnsideA315y_det_qb (x y cc : F) :
    (cc • burnsideA315y_qb x y).det = -(cc ^ 2 * (x ^ 2 + y ^ 2)) := by
  simp [burnsideA315y_qb, Matrix.det_fin_two]
  ring

theorem burnsideA315y_qb_mul_qa (x y cc : F) :
    (cc • burnsideA315y_qb x y) * burnsideA315y_qa F =
      -1 * burnsideA315y_qa F * (cc • burnsideA315y_qb x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315y_qa, burnsideA315y_qb, Matrix.mul_apply, Fin.sum_univ_two]

theorem burnsideA315y_blkMat_neg_one :
    blkMat (-1 : Matrix (Fin 2) (Fin 2) F) 1 = diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem burnsideA315y_blkMat_smul_neg_one :
    blkMat ((-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) 1 = diagonal ![-1, -1, 1] := by
  rw [neg_one_smul]
  exact burnsideA315y_blkMat_neg_one

end Quat

namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X]

@[expose] def C₁ (M : burnsideA315y_Model F X) : Subgroup ↥M.Γ := burnsideA315y_C1 M.Γ M.zh

theorem S₀_le_C₁ (M : burnsideA315y_Model F X) : M.S₀ ≤ M.C₁ := fun s hs =>
  ⟨M.S₀_det s hs, M.S₀_comm s hs⟩

section OfData

variable (Γ : Subgroup (GL (Fin 3) F)) (zh Da Db : ↥Γ) (x y cc : F)

theorem data_Da_sq (zh_val : (zh : GL (Fin 3) F) = negDiag3 F)
    (Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1) :
    Da ^ 2 = zh := by
  apply Subtype.ext
  apply Units.ext
  rw [zh_val, coe_negDiag3, sq, Subgroup.coe_mul, Units.val_mul, Da_val, blkMat_mul,
    burnsideA315y_qa_mul_qa, mul_one, burnsideA315y_blkMat_neg_one]

theorem data_Db_sq (zh_val : (zh : GL (Fin 3) F) = negDiag3 F)
    (Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (cc • burnsideA315y_qb x y) 1)
    (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) : Db ^ 2 = zh := by
  apply Subtype.ext
  apply Units.ext
  rw [zh_val, coe_negDiag3, sq, Subgroup.coe_mul, Units.val_mul, Db_val, blkMat_mul,
    burnsideA315y_qb_mul_qb, hdet, mul_one, burnsideA315y_blkMat_smul_neg_one]

theorem data_zh_sq (zh_val : (zh : GL (Fin 3) F) = negDiag3 F) : zh ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [sq, Subgroup.coe_mul, Units.val_mul, zh_val, coe_negDiag3, Subgroup.coe_one, Units.val_one,
    diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

theorem data_Db_Da (zh_val : (zh : GL (Fin 3) F) = negDiag3 F)
    (Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (cc • burnsideA315y_qb x y) 1) :
    Db * Da = zh * Da * Db := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [Da_val, Db_val, zh_val, coe_negDiag3, ← burnsideA315y_blkMat_neg_one, blkMat_mul, blkMat_mul,
    blkMat_mul, burnsideA315y_qb_mul_qa]
  simp

theorem data_mem_C1 (zh_val : (zh : GL (Fin 3) F) = negDiag3 F) (two_ne : (2 : F) ≠ 0)
    {g : ↥Γ} {A : Matrix (Fin 2) (Fin 2) F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat A 1) (hA : A.det = 1) :
    g ∈ burnsideA315y_C1 Γ zh := by
  refine ⟨by rw [hg, det_blkMat, hA, mul_one], ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hg, zh_val, coe_negDiag3, ← burnsideA315y_blkMat_neg_one, blkMat_mul, blkMat_mul]
  simp

theorem data_quat (zh_val : (zh : GL (Fin 3) F) = negDiag3 F) (two_ne : (2 : F) ≠ 0)
    (Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (cc • burnsideA315y_qb x y) 1)
    (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) :
    IsPGroup 2 ↥(Subgroup.zpowers Db ⊔ Subgroup.zpowers Da) ∧
      Subgroup.zpowers Db ⊔ Subgroup.zpowers Da ≤ burnsideA315y_C1 Γ zh := by
  have hDa2 := data_Da_sq Γ zh Da zh_val Da_val
  have hDb2 := data_Db_sq Γ zh Db x y cc zh_val Db_val hdet
  have hz2 := data_zh_sq Γ zh zh_val
  have hDa4 : Da ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hDa2, hz2]
  have hDb4 : Db ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hDb2, hz2]
  have hrel : Db * Da * Db⁻¹ = Da ^ 3 := by
    rw [data_Db_Da Γ zh Da Db x y cc zh_val Da_val Db_val, ← hDa2]
    group
  refine ⟨burnsideA315y_isPGroup_quat hDa4 hDb4 hrel, sup_le ?_ ?_⟩
  · rw [Subgroup.zpowers_le]
    refine data_mem_C1 Γ zh zh_val two_ne Db_val ?_
    rw [burnsideA315y_det_qb, hdet, neg_neg]
  · rw [Subgroup.zpowers_le]
    exact data_mem_C1 Γ zh zh_val two_ne Da_val burnsideA315y_det_qa

end OfData

@[expose] noncomputable def ofData (Γ : Subgroup (GL (Fin 3) F)) [Finite ↥Γ] (c : ↥Γ →* X)
    (ker_c : ∀ g : ↥Γ, c g = 1 ↔
      ∃ μ : Fˣ, (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ)
    (zh : ↥Γ) (zh_val : (zh : GL (Fin 3) F) = negDiag3 F) (x y cc : F)
    (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (Da Db : ↥Γ)
    (Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (cc • burnsideA315y_qb x y) 1)
    (two_ne : (2 : F) ≠ 0) : burnsideA315y_Model F X :=
  have hQ := data_quat Γ zh Da Db x y cc zh_val two_ne Da_val Db_val hdet
  have hS := burnsideA315y_exists_sylow_le hQ.1 hQ.2
  { Γ := Γ
    c := c
    ker_c := ker_c
    zh := zh
    zh_val := zh_val
    x := x
    y := y
    cc := cc
    hxy := by
      intro h0
      rw [h0, mul_zero] at hdet
      exact one_ne_zero (neg_eq_zero.mp hdet.symm)
    hcc := by
      intro h0
      rw [h0] at hdet
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hdet
      exact one_ne_zero (neg_eq_zero.mp hdet.symm)
    Da := Da
    Db := Db
    Da_val := Da_val
    Db_val := Db_val
    S₀ := Classical.choose hS
    S₀_two := (Classical.choose_spec hS).2.2.1
    zh_mem := by
      have h1 : zh ∈ Subgroup.zpowers Db ⊔ Subgroup.zpowers Da := by
        rw [← data_Da_sq Γ zh Da zh_val Da_val]
        exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers Da) 2)
      exact (Classical.choose_spec hS).1 h1
    Da_mem := (Classical.choose_spec hS).1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers Da))
    Db_mem := (Classical.choose_spec hS).1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers Db))
    S₀_comm := fun s hs => ((Classical.choose_spec hS).2.1 hs).2
    S₀_det := fun s hs => ((Classical.choose_spec hS).2.1 hs).1
    two_ne := two_ne }

theorem ofData_relIndex (Γ : Subgroup (GL (Fin 3) F)) [Finite ↥Γ] (c : ↥Γ →* X)
    (ker_c : ∀ g : ↥Γ, c g = 1 ↔
      ∃ μ : Fˣ, (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ)
    (zh : ↥Γ) (zh_val : (zh : GL (Fin 3) F) = negDiag3 F) (x y cc : F)
    (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (Da Db : ↥Γ)
    (Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (cc • burnsideA315y_qb x y) 1)
    (two_ne : (2 : F) ≠ 0) :
    ¬ 2 ∣ (ofData Γ c ker_c zh zh_val x y cc hdet Da Db Da_val Db_val two_ne).S₀.relIndex
      (ofData Γ c ker_c zh zh_val x y cc hdet Da Db Da_val Db_val two_ne).C₁ :=
  (Classical.choose_spec (burnsideA315y_exists_sylow_le
    (data_quat Γ zh Da Db x y cc zh_val two_ne Da_val Db_val hdet).1
    (data_quat Γ zh Da Db x y cc zh_val two_ne Da_val Db_val hdet).2)).2.2.2

end burnsideA315y_Model

end CFSG.ASVolI
