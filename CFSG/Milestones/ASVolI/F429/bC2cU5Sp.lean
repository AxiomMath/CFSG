module

public import CFSG.Milestones.ASVolI.F429.U4Graph
public import CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTBC
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

section SpEmb

@[expose] def burnsideF429b_U5_idx : HypIndex 2 1 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 1 where
  toFun a := match a with
    | .inl i => .inl (.inl i)
    | .inr (.inl k) => .inr k
    | .inr (.inr i) => .inl (.inr i)
  invFun a := match a with
    | .inl (.inl i) => .inl i
    | .inl (.inr i) => .inr (.inr i)
    | .inr k => .inr (.inl k)
  left_inv a := by rcases a with i | k | i <;> rfl
  right_inv a := by rcases a with (i | i) | k <;> rfl

theorem burnsideF429b_U5_idx_cases (a : HypIndex 2 1) :
    a = .inr (.inl 0) ∨ ∃ a', a = burnsideF429b_U5_idx.symm (.inl a') := by
  rcases a with i | k | i
  · exact Or.inr ⟨.inl i, rfl⟩
  · exact Or.inl (by rw [Subsingleton.elim k 0])
  · exact Or.inr ⟨.inr i, rfl⟩

theorem burnsideF429b_U5_idx_z : burnsideF429b_U5_idx (.inr (.inl 0)) = .inr 0 := rfl

theorem burnsideF429b_U5_idx_symm_ne (a : Fin 2 ⊕ Fin 2) :
    burnsideF429b_U5_idx.symm (.inl a) ≠ .inr (.inl 0) := by
  rcases a with i | i <;> simp [burnsideF429b_U5_idx]

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] noncomputable def burnsideF429b_U5_incl
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  ((fromBlocks A 0 0 1).map hK.fixedField.subtype).submatrix burnsideF429b_U5_idx
    burnsideF429b_U5_idx

theorem burnsideF429b_U5_incl_apply (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
    (a b : Fin 2 ⊕ Fin 2) :
    burnsideF429b_U5_incl hK A (burnsideF429b_U5_idx.symm (.inl a))
      (burnsideF429b_U5_idx.symm (.inl b)) = (A a b : K) := by
  simp [burnsideF429b_U5_incl]

theorem burnsideF429b_U5_incl_z_left (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
    (b : HypIndex 2 1) :
    burnsideF429b_U5_incl hK A (.inr (.inl 0)) b = if b = .inr (.inl 0) then 1 else 0 := by
  rcases burnsideF429b_U5_idx_cases b with rfl | ⟨b', rfl⟩
  · simp [burnsideF429b_U5_incl, burnsideF429b_U5_idx_z]
  · rw [if_neg (burnsideF429b_U5_idx_symm_ne b')]
    simp [burnsideF429b_U5_incl, burnsideF429b_U5_idx_z]

theorem burnsideF429b_U5_incl_z_right (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
    (a : HypIndex 2 1) :
    burnsideF429b_U5_incl hK A a (.inr (.inl 0)) = if a = .inr (.inl 0) then 1 else 0 := by
  rcases burnsideF429b_U5_idx_cases a with rfl | ⟨a', rfl⟩
  · simp [burnsideF429b_U5_incl, burnsideF429b_U5_idx_z]
  · rw [if_neg (burnsideF429b_U5_idx_symm_ne a')]
    simp [burnsideF429b_U5_incl, burnsideF429b_U5_idx_z]

theorem burnsideF429b_U5_incl_mul (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    burnsideF429b_U5_incl hK (A * B) =
      burnsideF429b_U5_incl hK A * burnsideF429b_U5_incl hK B := by
  have e : (fromBlocks (A * B) 0 0 1 :
      Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) hK.fixedField) =
      fromBlocks A 0 0 1 * fromBlocks B 0 0 1 := by
    rw [fromBlocks_multiply]
    simp
  rw [burnsideF429b_U5_incl, burnsideF429b_U5_incl, burnsideF429b_U5_incl, e, Matrix.map_mul,
    submatrix_mul_equiv]

theorem burnsideF429b_U5_incl_one :
    burnsideF429b_U5_incl hK (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) = 1 := by
  rw [burnsideF429b_U5_incl, fromBlocks_one, Matrix.map_one _ (map_zero _) (map_one _),
    submatrix_one_equiv]

theorem burnsideF429b_U5_incl_transpose
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    (burnsideF429b_U5_incl hK A)ᵀ = burnsideF429b_U5_incl hK Aᵀ := by
  rw [burnsideF429b_U5_incl, burnsideF429b_U5_incl, transpose_submatrix, ← transpose_map,
    fromBlocks_transpose, transpose_zero, transpose_zero, transpose_one]

theorem burnsideF429b_U5_incl_bar (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    (burnsideF429b_U5_incl hK A).map hK.bar = burnsideF429b_U5_incl hK A := by
  ext i j
  exact (hK.mem_fixedField).mp
    ((fromBlocks A 0 0 1) (burnsideF429b_U5_idx i) (burnsideF429b_U5_idx j)).2

theorem burnsideF429b_U5_incl_injective : Function.Injective (burnsideF429b_U5_incl hK) := by
  intro A B e
  ext a b
  have h := congrFun (congrFun e (burnsideF429b_U5_idx.symm (.inl a)))
    (burnsideF429b_U5_idx.symm (.inl b))
  rw [burnsideF429b_U5_incl_apply, burnsideF429b_U5_incl_apply] at h
  exact h

theorem burnsideF429b_U5_hypGram_eq :
    hypGram 2 1 K = burnsideF429b_U5_incl hK (CFSG.Quasithin.H13.U4Par.spJ hK.fixedField) := by
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField hK
  ext a b
  rw [hypGram_apply]
  rcases burnsideF429b_U5_idx_cases a with rfl | ⟨a', rfl⟩
  · rw [burnsideF429b_U5_incl_z_left, hypPartner_inr_inl]
  rcases burnsideF429b_U5_idx_cases b with rfl | ⟨b', rfl⟩
  · rw [burnsideF429b_U5_incl_z_right, if_neg (burnsideF429b_U5_idx_symm_ne a'),
      if_neg (fun h => burnsideF429b_U5_idx_symm_ne a' (by
        rw [← hypPartner_hypPartner (burnsideF429b_U5_idx.symm (.inl a')), ← h]; rfl))]
  rw [burnsideF429b_U5_incl_apply]
  rcases a' with i | i <;> rcases b' with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [burnsideF429b_U5_idx, CFSG.Quasithin.H13.U4Par.spJ, hypPartner, CharTwo.neg_eq]

theorem burnsideF429b_U5_det_incl (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    (burnsideF429b_U5_incl hK A).det = (A.det : K) := by
  rw [burnsideF429b_U5_incl, det_submatrix_equiv_self, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_fromBlocks_zero₂₁, det_one, mul_one]
  rfl

theorem burnsideF429b_U5_incl_mem (A : StatedSp 2 hK.fixedField) :
    ((burnsideF429b_U5_incl hK ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)).map hK.bar)ᵀ * hypGram 2 1 K *
        burnsideF429b_U5_incl hK ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) = hypGram 2 1 K ∧
      (burnsideF429b_U5_incl hK ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)).det = 1 := by
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField hK
  refine ⟨?_, ?_⟩
  · rw [burnsideF429b_U5_incl_bar, burnsideF429b_U5_incl_transpose, burnsideF429b_U5_hypGram_eq hK,
      ← burnsideF429b_U5_incl_mul, ← burnsideF429b_U5_incl_mul,
      CFSG.Quasithin.H13.U4Par.symp_of_mem_statedSp A.2]
  · rw [burnsideF429b_U5_det_incl, CFSG.Quasithin.H13.U4Par.det_eq_one_of_mem_statedSp A.2]
    rfl

@[expose] noncomputable def burnsideF429b_U5_inclGL (A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
    GL (HypIndex 2 1) K :=
  ⟨burnsideF429b_U5_incl hK (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField),
    burnsideF429b_U5_incl hK ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField),
    by rw [← burnsideF429b_U5_incl_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      burnsideF429b_U5_incl_one],
    by rw [← burnsideF429b_U5_incl_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      burnsideF429b_U5_incl_one]⟩

@[expose] noncomputable def burnsideF429b_U5_spEmb : StatedSp 2 hK.fixedField →* hypSU hK 2 1 where
  toFun A := ⟨burnsideF429b_U5_inclGL hK (A : GL (Fin 2 ⊕ Fin 2) hK.fixedField), by
    rw [mem_gramSU]
    exact burnsideF429b_U5_incl_mem hK A⟩
  map_one' := mat_injective (by
    change burnsideF429b_U5_incl hK ((1 : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) = 1
    rw [Units.val_one, burnsideF429b_U5_incl_one])
  map_mul' A B := mat_injective (by
    change burnsideF429b_U5_incl hK (((A * B : StatedSp 2 hK.fixedField) :
        GL (Fin 2 ⊕ Fin 2) hK.fixedField) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) =
      burnsideF429b_U5_incl hK ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) *
      burnsideF429b_U5_incl hK ((B : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
    rw [Subgroup.coe_mul, Units.val_mul, burnsideF429b_U5_incl_mul])

theorem burnsideF429b_U5_mat_spEmb (A : StatedSp 2 hK.fixedField) :
    mat (burnsideF429b_U5_spEmb hK A) = burnsideF429b_U5_incl hK
      ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :=
  rfl

theorem burnsideF429b_U5_spEmb_injective : Function.Injective (burnsideF429b_U5_spEmb hK) := by
  intro A B e
  have e1 := congrArg mat e
  rw [burnsideF429b_U5_mat_spEmb, burnsideF429b_U5_mat_spEmb] at e1
  exact Subtype.ext (Units.ext (burnsideF429b_U5_incl_injective hK e1))

theorem burnsideF429b_U5_exists_spEmb (g : hypSU hK 2 1)
    (hfix : ∀ a b, hK.bar (mat g a b) = mat g a b) :
    ∃ A : StatedSp 2 hK.fixedField, burnsideF429b_U5_spEmb hK A = g := by
  haveI : CharP K 2 := hK.charP
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField hK
  have hJ : (mat g)ᵀ * hypGram 2 1 K * mat g = hypGram 2 1 K :=
    CFSG.Quasithin.H13.F431.Un.OL5.un5tb_gram_of_fixed hK g hfix
  have hrow := CFSG.Quasithin.H13.F431.Un.OL5.un5tb_row_z hJ
  have hcol := CFSG.Quasithin.H13.F431.Un.OL5.un5tb_col_z hJ
  set A₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField := Matrix.of fun a b =>
    ⟨mat g (burnsideF429b_U5_idx.symm (.inl a)) (burnsideF429b_U5_idx.symm (.inl b)),
      hK.mem_fixedField.mpr (hfix _ _)⟩ with hA₀def
  have hA₀ : burnsideF429b_U5_incl hK A₀ = mat g := by
    ext a b
    rcases burnsideF429b_U5_idx_cases a with rfl | ⟨a', rfl⟩
    · rw [burnsideF429b_U5_incl_z_left]
      exact (hrow b).symm
    rcases burnsideF429b_U5_idx_cases b with rfl | ⟨b', rfl⟩
    · rw [burnsideF429b_U5_incl_z_right]
      exact (hcol _).symm
    rw [burnsideF429b_U5_incl_apply]
    rfl
  have hdet : A₀.det ≠ 0 := by
    intro h0
    have h1 := (mem_gramSU.mp g.2).2
    change (mat g).det = 1 at h1
    rw [← hA₀, burnsideF429b_U5_det_incl, h0] at h1
    exact zero_ne_one h1
  set A : GL (Fin 2 ⊕ Fin 2) hK.fixedField := Matrix.GeneralLinearGroup.mk'' A₀
    (isUnit_iff_ne_zero.mpr hdet) with hAdef
  have hAval : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) = A₀ := rfl
  have hAsp : A ∈ StatedSp 2 hK.fixedField := by
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hAval]
    apply burnsideF429b_U5_incl_injective hK
    rw [burnsideF429b_U5_incl_mul, burnsideF429b_U5_incl_mul, ← burnsideF429b_U5_incl_transpose,
      ← burnsideF429b_U5_hypGram_eq hK, hA₀]
    exact hJ
  exact ⟨⟨A, hAsp⟩, mat_injective (by rw [burnsideF429b_U5_mat_spEmb]; exact hA₀)⟩

theorem burnsideF429b_U5_mat_scalar_mul {z : hypSU hK 2 1} {c : Kˣ}
    (hz : (z : GL (HypIndex 2 1) K) = GeneralLinearGroup.scalar (HypIndex 2 1) c)
    (g : hypSU hK 2 1) (a b : HypIndex 2 1) : mat (z * g) a b = c * mat g a b := by
  rw [mat_mul]
  unfold mat
  rw [hz]
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem burnsideF429b_U5_exists_spEmb_of_fix {σ : K ≃+* K} (hσ : ∀ c, σ c = hK.bar c)
    (w : hypPSU hK 2 1)
    (hw : Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) w = w) :
    ∃ A : StatedSp 2 hK.fixedField, hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A) = w := by
  obtain ⟨g, rfl⟩ := hypProj_surjective hK 2 1 w
  rw [Phi_apply] at hw
  obtain ⟨z, hzdef⟩ : ∃ z : hypSU hK 2 1,
      z = act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) g * g⁻¹ :=
    ⟨_, rfl⟩
  have hzS : z ∈ hypScalars hK 2 1 := by
    rw [hzdef, ← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hw, mul_inv_cancel]
  obtain ⟨c, hcn, hc5, hcz⟩ := hzS
  have hzg : z * g = act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) g := by
    rw [hzdef, inv_mul_cancel_right]
  have hσg : ∀ a b, σ (mat g a b) = c * mat g a b := by
    intro a b
    have e1 := congrFun (congrFun
      (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.mat_act_fieldElt σ g) a) b
    rw [Matrix.map_apply] at e1
    rw [← e1, ← hzg, burnsideF429b_U5_mat_scalar_mul hK hcz]
  obtain ⟨g', hg'⟩ : ∃ g' : hypSU hK 2 1, g' = z * (z * (z * g)) := ⟨_, rfl⟩
  have hg'm : ∀ a b, mat g' a b = c * (c * (c * mat g a b)) := by
    intro a b
    rw [hg', burnsideF429b_U5_mat_scalar_mul hK hcz, burnsideF429b_U5_mat_scalar_mul hK hcz,
      burnsideF429b_U5_mat_scalar_mul hK hcz]
  have h1 : (c : K) * hK.bar c = 1 := hcn
  have h2 : (c : K) ^ 5 = 1 := by
    have := congrArg Units.val hc5
    simpa using this
  have hfix : ∀ a b, hK.bar (mat g' a b) = mat g' a b := by
    intro a b
    rw [hg'm, map_mul, map_mul, map_mul, ← hσ (mat g a b), hσg]
    linear_combination (mat g a b) * (hK.bar c ^ 2 + (c : K) ^ 3 * ((c : K) * hK.bar c + 1)) * h1 -
      (mat g a b) * hK.bar c ^ 2 * h2
  obtain ⟨A, hA⟩ := burnsideF429b_U5_exists_spEmb hK g' hfix
  refine ⟨A, ?_⟩
  have hz1 : hypProj hK 2 1 z = 1 := by
    rw [← MonoidHom.mem_ker, ker_hypProj]
    exact ⟨c, hcn, hc5, hcz⟩
  rw [hA, hg', map_mul, map_mul, map_mul, hz1, one_mul, one_mul, one_mul]

theorem burnsideF429b_U5_proj_spEmb_injective :
    Function.Injective ((hypProj hK 2 1).comp (burnsideF429b_U5_spEmb hK)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : burnsideF429b_U5_spEmb hK A ∈ hypScalars hK 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker]
    exact hA
  obtain ⟨c, -, -, hc⟩ := h1
  have h2 : mat (burnsideF429b_U5_spEmb hK A) (.inr (.inl 0)) (.inr (.inl 0)) = c := by
    unfold mat
    rw [hc]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  rw [burnsideF429b_U5_mat_spEmb, burnsideF429b_U5_incl_z_left, if_pos rfl] at h2
  have hc1 : c = 1 := Units.ext h2.symm
  apply burnsideF429b_U5_spEmb_injective hK
  rw [map_one]
  exact Subtype.ext (by rw [hc, hc1, map_one]; rfl)

theorem burnsideF429b_U5_rank_incl (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :
    Matrix.rank (burnsideF429b_U5_incl hK A - 1) = 1 ↔ Matrix.rank (A - 1) = 1 := by
  have e1 : burnsideF429b_U5_incl hK A - 1 =
      ((fromBlocks (A - 1) 0 0 0 :
        Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) hK.fixedField).map
          hK.fixedField.subtype).submatrix burnsideF429b_U5_idx burnsideF429b_U5_idx := by
    rw [← burnsideF429b_U5_incl_one hK]
    ext a b
    simp only [burnsideF429b_U5_incl, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.map_apply]
    generalize burnsideF429b_U5_idx a = a'
    generalize burnsideF429b_U5_idx b = b'
    rcases a' with a' | a' <;> rcases b' with b' | b' <;> simp
  have e2 : (fromBlocks (A - 1) 0 0 0 :
      Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) hK.fixedField) =
      fromRows (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
        (0 : Matrix (Fin 1) (Fin 2 ⊕ Fin 2) hK.fixedField) * (A - 1) *
      fromCols (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
        (0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 1) hK.fixedField) := by
    rw [fromRows_mul, fromRows_mul_fromCols]
    simp
  have hQP : fromCols (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
      (0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 1) hK.fixedField) *
      fromRows (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField)
        (0 : Matrix (Fin 1) (Fin 2 ⊕ Fin 2) hK.fixedField) = 1 := by
    rw [fromCols_mul_fromRows]
    simp
  rw [e1, Matrix.rank_submatrix, burnsideF429_rank_map_eq_one_iff, e2,
    burnsideF429_rank_sandwich _ _ hQP]

end SpEmb

section Cen

open CFSG.Quasithin CFSG.ASVolI.ChF

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)
  {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF429b_U5_cen_equiv (Ψ : hypPSU hK 2 1 ≃* ↥Gp) {t : E}
    (β u : MulAut (hypPSU hK 2 1))
    (hu : ∀ A, u (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A)) =
      hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))
    (hfixu : ∀ w, u w = w → ∃ A, hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A) = w)
    (ht : ∀ w, ((Ψ (β (u w)) : ↥Gp) : E) = t * ((Ψ (β w) : ↥Gp) : E) * t⁻¹) :
    ∃ ι : StatedSp 2 hK.fixedField ≃* cenIn Gp t, ∀ A,
      ((ι A : cenIn Gp t) : E) =
        ((Ψ (β (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))) : ↥Gp) : E) := by
  let φ₀ : StatedSp 2 hK.fixedField →* E :=
    Gp.subtype.comp (Ψ.toMonoidHom.comp (β.toMonoidHom.comp
      ((hypProj hK 2 1).comp (burnsideF429b_U5_spEmb hK))))
  have hφ₀ : ∀ A, φ₀ A = ((Ψ (β (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))) : ↥Gp) : E) :=
    fun A => rfl
  have hmem : ∀ A, φ₀ A ∈ cenIn Gp t := by
    intro A
    rw [hφ₀]
    refine Subgroup.mem_inf.mpr ⟨(Ψ _).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e := ht (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))
    rw [hu] at e
    calc ((Ψ (β (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))) : ↥Gp) : E) * t =
        (t * ((Ψ (β (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))) : ↥Gp) : E) * t⁻¹) * t := by
          rw [← e]
      _ = t * ((Ψ (β (hypProj hK 2 1 (burnsideF429b_U5_spEmb hK A))) : ↥Gp) : E) := by group
  let ψ : StatedSp 2 hK.fixedField →* cenIn Gp t := φ₀.codRestrict (cenIn Gp t) hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun A B hAB => ?_, fun e => ?_⟩
    · have h1 : φ₀ A = φ₀ B := congrArg (fun z : cenIn Gp t => (z : E)) hAB
      rw [hφ₀, hφ₀] at h1
      have h2 := β.injective (Ψ.injective (Subtype.ext h1))
      exact burnsideF429b_U5_proj_spEmb_injective hK h2
    · obtain ⟨e, he⟩ := e
      obtain ⟨heG, het⟩ := Subgroup.mem_inf.mp he
      obtain ⟨w, hw⟩ : ∃ w : hypPSU hK 2 1, w = β.symm (Ψ.symm ⟨e, heG⟩) := ⟨_, rfl⟩
      have hwe : ((Ψ (β w) : ↥Gp) : E) = e := by
        rw [hw, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      have het' : t * e * t⁻¹ = e := by
        rw [Subgroup.mem_centralizer_singleton_iff] at het
        rw [← het]
        group
      have hwfix : u w = w := by
        have e1 := ht w
        rw [hwe, het', ← hwe] at e1
        exact β.injective (Ψ.injective (Subtype.ext e1))
      obtain ⟨A, hA⟩ := hfixu w hwfix
      refine ⟨A, Subtype.ext ?_⟩
      show φ₀ A = e
      rw [hφ₀, hA, hwe]
  exact ⟨MulEquiv.ofBijective ψ hψ, fun A => rfl⟩

theorem burnsideF429b_U5_coe_spEmb (A : StatedSp 2 hK.fixedField) :
    (((burnsideF429b_U5_spEmb hK A : hypSU hK 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = burnsideF429b_U5_incl hK
        ((A : GL (Fin 2 ⊕ Fin 2) hK.fixedField) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) hK.fixedField) :=
  rfl

theorem burnsideF429b_U5_fieldElt_spEmb {σ : K ≃+* K} (hσ : ∀ c, σ c = hK.bar c)
    (A : StatedSp 2 hK.fixedField) :
    act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ)
      (burnsideF429b_U5_spEmb hK A) = burnsideF429b_U5_spEmb hK A := by
  apply mat_injective
  rw [CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.mat_act_fieldElt, burnsideF429b_U5_mat_spEmb]
  ext a b
  rw [Matrix.map_apply, hσ]
  exact congrFun (congrFun (burnsideF429b_U5_incl_bar hK _) a) b

theorem burnsideF429b_U5_rank_act {y : Gam hK} (hy : y.1.right = 1) (g : hypSU hK 2 1) :
    Matrix.rank ((((act hK y g : hypSU hK 2 1) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1) =
      Matrix.rank ((((g : hypSU hK 2 1) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1) := by
  haveI : CharP K 2 := hK.charP
  have e : (((act hK y g : hypSU hK 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1 =
      ((y.1.left : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
        ((((g : hypSU hK 2 1) : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1) *
        (((y.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
    change ((y.1.left * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut y.1.right
      (g : GL (HypIndex 2 1) K) * y.1.left⁻¹ :
      GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1 = _
    rw [hy, map_one, MulAut.one_apply]
    exact burnsideF429_conj_sub_one y.1.left (g : GL (HypIndex 2 1) K)
  rw [e, burnsideF429_rank_conj]

theorem burnsideF429b_U5_isGenLie (Ψ : hypPSU hK 2 1 ≃* ↥Gp) {t : E} (β : MulAut (hypPSU hK 2 1))
    {σ : K ≃+* K} (hσ : ∀ c, σ c = hK.bar c)
    (ht : ∀ w, ((Ψ (β (Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) w)) :
      ↥Gp) : E) = t * ((Ψ (β w) : ↥Gp) : E) * t⁻¹) :
    IsGenLie ↥(cenIn Gp t) .Sp4 2 f := by
  obtain ⟨ι, -⟩ := burnsideF429b_U5_cen_equiv hK Ψ β
    (Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ))
    (fun A => by rw [Phi_apply, burnsideF429b_U5_fieldElt_spEmb hK hσ])
    (fun w hw => burnsideF429b_U5_exists_spEmb_of_fix hK hσ w hw) ht
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField hK
  haveI : Finite K := hK.finite
  exact ⟨Nat.prime_two, hK.one_le, hK.fixedField, inferInstance, inferInstance,
    hK.card_fixedField, ⟨ι.symm.trans (CFSG.QuasithinUnique.Lin2.Five.projEquiv _)⟩⟩

theorem burnsideF429b_U5_graphFixed (chart : NativeChart .U5 2 f Gp) (Ψ : hypPSU hK 2 1 ≃* ↥Gp)
    {t : E} {y : Gam hK} (hy : y.1.right = 1) {σ : K ≃+* K} (hσ : ∀ c, σ c = hK.bar c)
    (ht : ∀ w, ((Ψ (Phi hK y (Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ)
      w)) : ↥Gp) : E) = t * ((Ψ (Phi hK y w) : ↥Gp) : E) * t⁻¹)
    (hcrit : ∀ w : hypSU hK 2 1, w * w = 1 →
      (chart.coordinatePayload.RankInvolution 1 ((Ψ (hypProj hK 2 1 w) : ↥Gp) : E) ↔
        ((Ψ (hypProj hK 2 1 w) : ↥Gp) : E) ≠ 1 ∧
          Matrix.rank (((w : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1) =
            1)) :
    chart.GraphFixedMarkingGoal t := by
  intro _
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField hK
  haveI : Finite K := hK.finite
  obtain ⟨ι, hι⟩ := burnsideF429b_U5_cen_equiv hK Ψ (Phi hK y)
    (Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ))
    (fun A => by rw [Phi_apply, burnsideF429b_U5_fieldElt_spEmb hK hσ])
    (fun w hw => burnsideF429b_U5_exists_spEmb_of_fix hK hσ w hw) ht
  refine burnsideF429_sp4_marking_exists hK.one_le hK.card_fixedField ι
    (chart.coordinatePayload.RankInvolution 1) ?_ ?_
  · intro e he
    generalize chart.coordinatePayload = cp at he
    cases cp with
    | classical c hk marking => exact ⟨he.2.1, he.2.2.1⟩
    | g2 => exact (he : False).elim
    | g2Derived => exact (he : False).elim
    | triality => exact (he : False).elim
    | ree => exact (he : False).elim
    | tits => exact (he : False).elim
  · intro x hx1 hx2
    obtain ⟨w, hw⟩ : ∃ w : hypSU hK 2 1, w = act hK y (burnsideF429b_U5_spEmb hK x) := ⟨_, rfl⟩
    have hιx : ((ι x : cenIn Gp t) : E) = ((Ψ (hypProj hK 2 1 w) : ↥Gp) : E) := by
      rw [hι x, Phi_apply, hw]
    have hxx : x * x = 1 := by
      apply ι.injective
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul]
      exact hx2
    have hww : w * w = 1 := by
      rw [hw, ← act_mul, ← map_mul, hxx, map_one, act_one]
    rw [hιx, hcrit w hww, ← hιx, hw, burnsideF429b_U5_rank_act hK hy, burnsideF429b_U5_coe_spEmb,
      burnsideF429b_U5_rank_incl]
    exact ⟨fun h => h.2, fun h => ⟨hx1, h⟩⟩

theorem burnsideF429b_U5_ht_of_act (Ψ : hypPSU hK 2 1 ≃* ↥Gp) {t : E} (y : Gam hK) (σ : K ≃+* K)
    (ht : ∀ g : hypSU hK 2 1, ((Ψ (hypProj hK 2 1 (act hK y
      (act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) g))) : ↥Gp) : E) =
        t * ((Ψ (hypProj hK 2 1 (act hK y g)) : ↥Gp) : E) * t⁻¹)
    (w : hypPSU hK 2 1) :
    ((Ψ (Phi hK y (Phi hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK σ) w)) :
      ↥Gp) : E) = t * ((Ψ (Phi hK y w) : ↥Gp) : E) * t⁻¹ := by
  obtain ⟨g, rfl⟩ := hypProj_surjective hK 2 1 w
  rw [Phi_apply, Phi_apply, Phi_apply]
  exact ht g

theorem burnsideF429b_U5_isGenLie_act (Ψ : hypPSU hK 2 1 ≃* ↥Gp) {t : E} (y : Gam hK)
    (ht : ∀ g : hypSU hK 2 1, ((Ψ (hypProj hK 2 1 (act hK y
      (act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK
        (CFSG.Quasithin.H13.U4Par.barEquiv hK)) g))) : ↥Gp) : E) =
        t * ((Ψ (hypProj hK 2 1 (act hK y g)) : ↥Gp) : E) * t⁻¹) :
    IsGenLie ↥(cenIn Gp t) .Sp4 2 f :=
  burnsideF429b_U5_isGenLie hK Ψ (Phi hK y) (CFSG.Quasithin.H13.U4Par.barEquiv_apply hK)
    (burnsideF429b_U5_ht_of_act hK Ψ y _ ht)

theorem burnsideF429b_U5_graphFixed_act (chart : NativeChart .U5 2 f Gp)
    (Ψ : hypPSU hK 2 1 ≃* ↥Gp) {t : E} {y : Gam hK} (hy : y.1.right = 1)
    (ht : ∀ g : hypSU hK 2 1, ((Ψ (hypProj hK 2 1 (act hK y
      (act hK (CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution.fieldElt hK
        (CFSG.Quasithin.H13.U4Par.barEquiv hK)) g))) : ↥Gp) : E) =
        t * ((Ψ (hypProj hK 2 1 (act hK y g)) : ↥Gp) : E) * t⁻¹)
    (hcrit : ∀ w : hypSU hK 2 1, w * w = 1 →
      (chart.coordinatePayload.RankInvolution 1 ((Ψ (hypProj hK 2 1 w) : ↥Gp) : E) ↔
        ((Ψ (hypProj hK 2 1 w) : ↥Gp) : E) ≠ 1 ∧
          Matrix.rank (((w : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) - 1) =
            1)) :
    chart.GraphFixedMarkingGoal t :=
  burnsideF429b_U5_graphFixed hK chart Ψ hy (CFSG.Quasithin.H13.U4Par.barEquiv_apply hK)
    (burnsideF429b_U5_ht_of_act hK Ψ y _ ht) hcrit

end Cen

end CFSG.ASVolI
