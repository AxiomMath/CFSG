module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.SpM

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

variable {K : Type} [Field K]

@[expose] noncomputable def u (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : StatedSp 2 K :=
  upperUnipotentSp 2 K hC

theorem spMat_u (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) :
    spMat (u C hC) = fromBlocks 1 C 0 1 :=
  coe_upperUnipotentSp hC

theorem u_mul (C C' : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) (hC' : C'ᵀ = C') :
    u C hC * u C' hC' = u (C + C') (by rw [transpose_add, hC, hC']) := by
  apply statedSp_ext
  show spMat (u C hC) * spMat (u C' hC') = spMat (u (C + C') _)
  rw [spMat_u, spMat_u, spMat_u, fromBlocks_multiply]
  simp [add_comm]

theorem u_zero : u (0 : Matrix (Fin 2) (Fin 2) K) (transpose_zero) = 1 := by
  apply statedSp_ext
  show spMat (u 0 _) = spMat 1
  rw [spMat_u, spMat_one, fromBlocks_one]

theorem u_inv (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) :
    (u C hC)⁻¹ = u (-C) (by rw [transpose_neg, hC]) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, u_mul]
  simp only [neg_add_cancel]
  exact u_zero

@[expose] noncomputable def ell (A : GL (Fin 2) K) : StatedSp 2 K := leviSp A

theorem spMat_ell (A : GL (Fin 2) K) :
    spMat (ell A) = fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
  coe_leviSp A

theorem ell_u_ell (A : GL (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) :
    ell A * u C hC * (ell A)⁻¹ =
      u ((A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  have hinv : (ell A)⁻¹ = ell A⁻¹ := (map_inv leviSp A).symm
  rw [hinv]
  apply statedSp_ext
  show spMat (ell A) * spMat (u C hC) * spMat (ell A⁻¹) = spMat (u _ _)
  rw [spMat_ell, spMat_u, spMat_ell, spMat_u, fromBlocks_multiply, fromBlocks_multiply]
  have h2 : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ *
      (((A⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    rw [inv_inv, ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp [Matrix.mul_assoc]
  · simp
  · simpa using h2

theorem ell_mul (A B : GL (Fin 2) K) : ell A * ell B = ell (A * B) := (map_mul leviSp A B).symm

theorem ell_inv (A : GL (Fin 2) K) : (ell A)⁻¹ = ell A⁻¹ := (map_inv leviSp A).symm

theorem comm_ell_u (A : GL (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) :
    ell A * u C hC * (ell A)⁻¹ * (u C hC)⁻¹ =
      u ((A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ - C)
        (by rw [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hC,
          Matrix.mul_assoc]) := by
  rw [ell_u_ell, u_inv, u_mul]
  congr 1
  abel

@[expose] def upT (s : K) : SpecialLinearGroup (Fin 2) K := ⟨!![1, s; 0, 1], by simp⟩

@[expose] def dT (δ : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(δ : K), 0; 0, ((δ⁻¹ : Kˣ) : K)], by simp⟩

theorem coe_dT (δ : Kˣ) : ((SpecialLinearGroup.toGL (dT δ) : GL (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = !![(δ : K), 0; 0, ((δ⁻¹ : Kˣ) : K)] := rfl

theorem coe_upT (s : K) : ((SpecialLinearGroup.toGL (upT s) : GL (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1] := rfl

@[expose] def dGL (δ : Kˣ) : GL (Fin 2) K :=
  ⟨!![1, 0; 0, (δ : K)], !![1, 0; 0, ((δ⁻¹ : Kˣ) : K)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[expose] def upGL (s : K) : GL (Fin 2) K :=
  ⟨!![1, s; 0, 1], !![1, -s; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem coe_dGL (δ : Kˣ) : ((dGL δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; 0, (δ : K)] := rfl

theorem coe_dGL_inv (δ : Kˣ) : (((dGL δ)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 0; 0, ((δ⁻¹ : Kˣ) : K)] := rfl

theorem coe_upGL (s : K) : ((upGL s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, s; 0, 1] := rfl

theorem coe_upGL_inv (s : K) : (((upGL s)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, -s; 0, 1] := rfl

@[expose] def e11 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]
@[expose] def e22 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]
@[expose] def eAlt : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem e11_sym : (e11 : Matrix (Fin 2) (Fin 2) K)ᵀ = e11 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem e22_sym : (e22 : Matrix (Fin 2) (Fin 2) K)ᵀ = e22 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem eAlt_sym : (eAlt : Matrix (Fin 2) (Fin 2) K)ᵀ = eAlt := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem smul_sym {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (c : K) : (c • C)ᵀ = c • C := by
  rw [transpose_smul, hC]

theorem sym_decomp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    C = C 0 0 • e11 + C 1 1 • e22 + C 0 1 • eAlt := by
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    simpa using this
  ext i j; fin_cases i <;> fin_cases j <;> simp [e11, e22, eAlt, h10]

theorem u_congr {C C' : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hC' : C'ᵀ = C') (h : C = C') :
    u C hC = u C' hC' := by
  subst h
  rfl

theorem u_mem_Q2 (j : Fin 2) (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ Q2 K j := by
  have hle : (j : ℕ) + 1 ≤ 2 := by have := j.isLt; omega
  have key : ∀ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) (v : Fin 2 ⊕ Fin 2 → K),
      v ∈ flag 2 K ((j : ℕ) + 1) → spMat (u C hC) *ᵥ v ∈ flag 2 K ((j : ℕ) + 1) := by
    intro C hC v hv
    rw [mem_flag_of_le hle, mem_isoFlag] at hv ⊢
    have hvr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext fun i => hv.1 i
    rw [spMat_u, fromBlocks_mulVec, hvr]
    refine ⟨fun i => by simp, fun i hi => ?_⟩
    simpa using hv.2 i hi
  refine mem_stabilizer_of_mulVec_mem (key C hC) fun v hv => ?_
  rw [u_inv]
  exact key _ _ v hv

theorem ell_mem_Q2_one (A : GL (Fin 2) K) : ell A ∈ Q2 K 1 := by
  have key : ∀ (A : GL (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K),
      v ∈ flag 2 K 2 → spMat (ell A) *ᵥ v ∈ flag 2 K 2 := by
    intro A v hv
    rw [mem_flag_of_le (le_refl 2), mem_isoFlag] at hv ⊢
    have hvr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext fun i => hv.1 i
    rw [spMat_ell, fromBlocks_mulVec, hvr]
    refine ⟨fun i => by simp, fun i hi => ?_⟩
    have : (i : ℕ) < 2 := i.isLt
    omega
  refine mem_stabilizer_of_mulVec_mem (key A) fun v hv => ?_
  rw [ell_inv]
  exact key _ v hv

theorem ell_mem_Q2_zero (A : GL (Fin 2) K) (hA : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hA' : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) : ell A ∈ Q2 K 0 := by
  have key : ∀ (A : GL (Fin 2) K), (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
      ∀ (v : Fin 2 ⊕ Fin 2 → K), v ∈ flag 2 K 1 → spMat (ell A) *ᵥ v ∈ flag 2 K 1 := by
    intro A hA v hv
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hv ⊢
    have hvr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext fun i => hv.1 i
    have hv1 : v (Sum.inl 1) = 0 := hv.2 1 (by norm_num)
    rw [spMat_ell, fromBlocks_mulVec, hvr]
    refine ⟨fun i => by simp, fun i hi => ?_⟩
    have hi1 : i = 1 := by
      fin_cases i
      · exact absurd hi (by norm_num)
      · rfl
    subst hi1
    simp [hA, hv1]
  refine mem_stabilizer_of_mulVec_mem (key A hA) fun v hv => ?_
  rw [ell_inv]
  exact key _ hA' v hv

theorem spLevi_one_eq (A : SpecialLinearGroup (Fin 2) K) :
    spLevi 1 A = ell (SpecialLinearGroup.toGL A) := by
  simp [spLevi, ell]

@[expose] def uSet : Set (StatedSp 2 K) :=
  {g | ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C), u C hC = g}

@[expose] noncomputable def H1 : Subgroup (StatedSp 2 K) :=
  (spLevi (K := K) 1).range ⊔ Subgroup.closure uSet

theorem H1_le : H1 (K := K) ≤ Q2 K 1 := by
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨A, rfl⟩
    exact spLevi_mem 1 A
  · rintro _ ⟨C, hC, rfl⟩
    exact u_mem_Q2 1 C hC

theorem u_mem_H1 (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ H1 (K := K) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨C, hC, rfl⟩)

theorem ell_mem_H1 (A : SpecialLinearGroup (Fin 2) K) :
    ell (SpecialLinearGroup.toGL A) ∈ H1 (K := K) :=
  Subgroup.mem_sup_left ⟨A, spLevi_one_eq A⟩

theorem u_e11_mem (δ : Kˣ) (hδ : (δ : K) ^ 2 ≠ 1) (a : K) :
    u (a • e11) (smul_sym e11_sym a) ∈ ⁅H1 (K := K), H1 (K := K)⁆ := by
  have h := Subgroup.commutator_mem_commutator (ell_mem_H1 (dT δ))
    (u_mem_H1 ((a / ((δ : K) ^ 2 - 1)) • e11) (smul_sym e11_sym _))
  rw [commutatorElement_def, comm_ell_u] at h
  convert h using 2
  rw [coe_dT]
  have hd : (δ : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hδ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  field_simp

theorem u_e22_mem (δ : Kˣ) (hδ : (δ : K) ^ 2 ≠ 1) (a : K) :
    u (a • e22) (smul_sym e22_sym a) ∈ ⁅H1 (K := K), H1 (K := K)⁆ := by
  have hδ' : ((δ⁻¹ : Kˣ) : K) ^ 2 ≠ 1 := by
    intro h
    apply hδ
    have h2 : ((δ : K) * ((δ⁻¹ : Kˣ) : K)) ^ 2 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
    rw [mul_pow, h, mul_one] at h2
    exact h2
  have h := Subgroup.commutator_mem_commutator (ell_mem_H1 (dT δ))
    (u_mem_H1 ((a / (((δ⁻¹ : Kˣ) : K) ^ 2 - 1)) • e22) (smul_sym e22_sym _))
  rw [commutatorElement_def, comm_ell_u] at h
  convert h using 2
  rw [coe_dT]
  have hd : ((δ⁻¹ : Kˣ) : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hδ'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e22, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  field_simp

theorem u_eAlt_mem (δ : Kˣ) (hδ : (δ : K) ^ 2 ≠ 1) (b : K) :
    u (b • eAlt) (smul_sym eAlt_sym b) ∈ ⁅H1 (K := K), H1 (K := K)⁆ := by
  have h := Subgroup.commutator_mem_commutator (ell_mem_H1 (upT 1))
    (u_mem_H1 (b • e22) (smul_sym e22_sym b))
  rw [commutatorElement_def, comm_ell_u] at h
  have h11 := u_e11_mem δ hδ (-b)
  have hm := (⁅H1 (K := K), H1 (K := K)⁆).mul_mem h h11
  rw [u_mul] at hm
  convert hm using 2
  rw [coe_upT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e11, e22, eAlt, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Matrix.vecTail]

theorem u_mem_comm_H1 (δ : Kˣ) (hδ : (δ : K) ^ 2 ≠ 1) (C : Matrix (Fin 2) (Fin 2) K)
    (hC : Cᵀ = C) : u C hC ∈ ⁅H1 (K := K), H1 (K := K)⁆ := by
  have h := (⁅H1 (K := K), H1 (K := K)⁆).mul_mem
    ((⁅H1 (K := K), H1 (K := K)⁆).mul_mem (u_e11_mem δ hδ (C 0 0))
      (u_e22_mem δ hδ (C 1 1))) (u_eAlt_mem δ hδ (C 0 1))
  rw [u_mul, u_mul] at h
  convert h using 2
  exact sym_decomp hC

theorem perfect_H1 (hK : ∃ s : Finset K, s.card = 4) (δ : Kˣ) (hδ : (δ : K) ^ 2 ≠ 1) :
    ⁅H1 (K := K), H1 (K := K)⁆ = H1 (K := K) := by
  refine le_antisymm (A3.commutator_self_le (H1 (K := K)))
    (sup_le ?_ ((Subgroup.closure_le _).2 ?_))
  · rw [← spLevi_range_perfect hK 1]
    exact Subgroup.commutator_mono le_sup_left le_sup_left
  · rintro _ ⟨C, hC, rfl⟩
    exact u_mem_comm_H1 δ hδ C hC

@[expose] noncomputable def x (s : K) : StatedSp 2 K := ell (upGL s)

theorem x_mem_Q2 (s : K) : x s ∈ Q2 K 0 :=
  ell_mem_Q2_zero _ (by rw [coe_upGL]; simp) (by rw [coe_upGL_inv]; simp)

theorem spLevi_zero_dT (δ : Kˣ) : spLevi 0 (dT δ) = ell (dGL δ) := by
  apply statedSp_ext
  show spMat (spLevi 0 (dT δ)) = spMat (ell (dGL δ))
  rw [spMat_lam, spMat_ell, coe_dGL, coe_dGL_inv]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairMat, dT]

theorem spLevi_zero_upT (c : K) : spLevi 0 (upT c) = u (c • e22) (smul_sym e22_sym c) := by
  apply statedSp_ext
  show spMat (spLevi 0 (upT c)) = spMat (u _ _)
  rw [spMat_lam, spMat_u]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairMat, upT, e22]

@[expose] noncomputable def H0 : Subgroup (StatedSp 2 K) :=
  (spLevi (K := K) 0).range ⊔ Subgroup.closure ({g | ∃ s : K, x s = g} ∪ uSet)

theorem H0_le : H0 (K := K) ≤ Q2 K 0 := by
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨A, rfl⟩
    exact spLevi_mem 0 A
  · rintro _ (⟨s, rfl⟩ | ⟨C, hC, rfl⟩)
    · exact x_mem_Q2 s
    · exact u_mem_Q2 0 C hC

theorem x_mem_H0 (s : K) : x s ∈ H0 (K := K) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨s, rfl⟩))

theorem u_mem_H0 (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) : u C hC ∈ H0 (K := K) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨C, hC, rfl⟩))

theorem range_le_comm_H0 (hK : ∃ s : Finset K, s.card = 4) :
    (spLevi (K := K) 0).range ≤ ⁅H0 (K := K), H0 (K := K)⁆ := by
  rw [← spLevi_range_perfect hK 0]
  exact Subgroup.commutator_mono le_sup_left le_sup_left

theorem x_mem_comm_H0 (δ : Kˣ) (hδ : (δ : K) ≠ 1) (s : K) :
    x s ∈ ⁅H0 (K := K), H0 (K := K)⁆ := by
  have hδ' : ((δ⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
    intro h
    apply hδ
    have h1 : ((δ⁻¹ : Kˣ) : K) = 1 := sub_eq_zero.mp h
    have h2 : (δ : K) * ((δ⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, mul_one] at h2
    exact h2
  have hD : ell (dGL δ) ∈ H0 (K := K) :=
    Subgroup.mem_sup_left ⟨dT δ, spLevi_zero_dT δ⟩
  have h := Subgroup.commutator_mem_commutator hD (x_mem_H0 (s / (((δ⁻¹ : Kˣ) : K) - 1)))
  convert h using 1
  rw [commutatorElement_def, x, x, ell_inv, ell_inv, ell_mul, ell_mul, ell_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dGL, coe_dGL_inv, coe_upGL, coe_upGL_inv,
    coe_upGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp
  ring

theorem u_eAlt_mem_H0 (δ : Kˣ) (hδ : (δ : K) ≠ 1) (b : K) :
    u (b • eAlt) (smul_sym eAlt_sym b) ∈ ⁅H0 (K := K), H0 (K := K)⁆ := by
  have hD : ell (dGL δ) ∈ H0 (K := K) :=
    Subgroup.mem_sup_left ⟨dT δ, spLevi_zero_dT δ⟩
  have h := Subgroup.commutator_mem_commutator hD
    (u_mem_H0 ((b / ((δ : K) - 1)) • eAlt) (smul_sym eAlt_sym _))
  rw [commutatorElement_def, comm_ell_u] at h
  convert h using 2
  rw [coe_dGL]
  have hd : (δ : K) - 1 ≠ 0 := sub_ne_zero.mpr hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eAlt, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail] <;> field_simp

theorem u_e22_mem_H0 (hK : ∃ s : Finset K, s.card = 4) (c : K) :
    u (c • e22) (smul_sym e22_sym c) ∈ ⁅H0 (K := K), H0 (K := K)⁆ := by
  rw [← spLevi_zero_upT c]
  exact range_le_comm_H0 hK ⟨upT c, rfl⟩

theorem u_e11_mem_H0 [Finite K] [CharP K 2] (δ : Kˣ) (hδ : (δ : K) ≠ 1) (a : K) :
    u (a • e11) (smul_sym e11_sym a) ∈ ⁅H0 (K := K), H0 (K := K)⁆ := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  have hE : u (1 • e22) (smul_sym e22_sym 1) ∈ H0 (K := K) := u_mem_H0 _ _
  have h := Subgroup.commutator_mem_commutator hE (x_mem_H0 r)
  rw [commutatorElement_def, x, mul_assoc, mul_assoc, ← mul_assoc (ell (upGL r)), u_inv,
    ell_u_ell, u_mul] at h
  have h2 := (⁅H0 (K := K), H0 (K := K)⁆).mul_mem h (u_eAlt_mem_H0 δ hδ r)
  rw [u_mul] at h2
  convert h2 using 2
  rw [coe_upGL, hr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e11, e22, eAlt, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem u_mem_comm_H0 [Finite K] [CharP K 2] (hK : ∃ s : Finset K, s.card = 4) (δ : Kˣ)
    (hδ : (δ : K) ≠ 1) (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) :
    u C hC ∈ ⁅H0 (K := K), H0 (K := K)⁆ := by
  have h := (⁅H0 (K := K), H0 (K := K)⁆).mul_mem
    ((⁅H0 (K := K), H0 (K := K)⁆).mul_mem (u_e11_mem_H0 δ hδ (C 0 0))
      (u_e22_mem_H0 hK (C 1 1))) (u_eAlt_mem_H0 δ hδ (C 0 1))
  rw [u_mul, u_mul] at h
  convert h using 2
  exact sym_decomp hC

theorem perfect_H0 [Finite K] [CharP K 2] (hK : ∃ s : Finset K, s.card = 4) (δ : Kˣ)
    (hδ : (δ : K) ≠ 1) : ⁅H0 (K := K), H0 (K := K)⁆ = H0 (K := K) := by
  refine le_antisymm (A3.commutator_self_le (H0 (K := K)))
    (sup_le (range_le_comm_H0 hK) ((Subgroup.closure_le _).2 ?_))
  rintro _ (⟨s, rfl⟩ | ⟨C, hC, rfl⟩)
  · exact x_mem_comm_H0 δ hδ s
  · exact u_mem_comm_H0 hK δ hδ C hC

end CFSG.Quasithin.H13.Ch9.KGFF.SpM
