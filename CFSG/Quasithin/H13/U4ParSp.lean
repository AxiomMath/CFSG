module

public import CFSG.Quasithin.H13.U4ParOuterO2
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (weylRep)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

abbrev spJ (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 (-1) 0

theorem symp_of_mem_statedSp {F : Type} [Field F] {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : A ∈ StatedSp 2 F) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = spJ F := by
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, transpose_mul]
    calc (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * (x : Matrix _ _ F)ᵀ * spJ F *
          ((x : Matrix _ _ F) * (y : Matrix _ _ F)) =
        (y : Matrix _ _ F)ᵀ * ((x : Matrix _ _ F)ᵀ * spJ F * (x : Matrix _ _ F)) *
          (y : Matrix _ _ F) := by simp only [Matrix.mul_assoc]
      _ = spJ F := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F *
          ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) =
        ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F)ᵀ *
          ((x : Matrix _ _ F)ᵀ * spJ F * (x : Matrix _ _ F)) *
          ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) := by rw [hx]
      _ = ((x : Matrix _ _ F) * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F))ᵀ * spJ F *
          ((x : Matrix _ _ F) * ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F)) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = spJ F := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem det_spJ_ne_zero (F : Type) [Field F] : (spJ F).det ≠ 0 := by
  intro h0
  have e : spJ F * spJ F = -1 := by
    rw [spJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
    simp
  have := congrArg Matrix.det e
  rw [det_mul, h0, zero_mul, det_neg, det_one, Fintype.card_sum, Fintype.card_fin] at this
  norm_num at this

theorem det_eq_one_of_mem_statedSp {F : Type} [Field F] [CharP F 2] {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : A ∈ StatedSp 2 F) : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det = 1 := by
  have e := congrArg Matrix.det (symp_of_mem_statedSp hA)
  rw [det_mul, det_mul, det_transpose] at e
  have e' : ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det - 1) * (spJ F).det = 0 := by
    linear_combination e
  exact eq_one_of_mul_self_eq_one (sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right
    (det_spJ_ne_zero F)))

@[expose] noncomputable def inclMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :
    Matrix Ix Ix K :=
  (A.map h.fixedField.subtype).submatrix ixEF ixEF

theorem inclMat_apply (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) (i j : Ix) :
    inclMat h A i j = (A (ixEF i) (ixEF j) : K) :=
  rfl

theorem inclMat_mul (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :
    inclMat h (A * B) = inclMat h A * inclMat h B := by
  rw [inclMat, inclMat, inclMat, submatrix_mul_equiv, Matrix.map_mul]

theorem inclMat_one : inclMat h (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) = 1 := by
  rw [inclMat, Matrix.map_one _ (map_zero _) (map_one _), submatrix_one_equiv]

theorem inclMat_transpose (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :
    (inclMat h A)ᵀ = inclMat h Aᵀ := by
  ext i j
  rfl

theorem inclMat_bar (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :
    (inclMat h A).map h.bar = inclMat h A := by
  ext i j
  exact (h.mem_fixedField).mp (A (ixEF i) (ixEF j)).2

theorem inclMat_injective : Function.Injective (inclMat (K := K) h) := by
  intro A B e
  ext a b
  have := congrFun (congrFun e (ixEF.symm a)) (ixEF.symm b)
  rw [inclMat_apply, inclMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this

theorem hypGram_eq_inclMat : hypGram 2 0 K = inclMat h (spJ h.fixedField) := by
  have := charP_fixedField h
  ext i j
  rw [inclMat_apply, hypGram_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [spJ, ixEF, ie1, ie2, if1, if2, hypPartner, CharTwo.neg_eq]

theorem det_inclMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :
    (inclMat h A).det = (A.det : K) := by
  rw [inclMat, det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

theorem inclMat_mem (A : StatedSp 2 h.fixedField) :
    ((inclMat h ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix _ _ h.fixedField)).map h.bar)ᵀ *
        hypGram 2 0 K * inclMat h ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix _ _ _) =
      hypGram 2 0 K ∧
    (inclMat h ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix _ _ h.fixedField)).det = 1 := by
  have := charP_fixedField h
  refine ⟨?_, ?_⟩
  · rw [inclMat_bar, inclMat_transpose, hypGram_eq_inclMat h, ← inclMat_mul, ← inclMat_mul,
      symp_of_mem_statedSp A.2]
  · rw [det_inclMat, det_eq_one_of_mem_statedSp A.2]
    rfl

@[expose] noncomputable def inclGL (A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : GL Ix K :=
  ⟨inclMat h (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField),
    inclMat h ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField),
    by rw [← inclMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, inclMat_one],
    by rw [← inclMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, inclMat_one]⟩

theorem coe_inclGL (A : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
    ((inclGL h A : GL Ix K) : Matrix Ix Ix K) =
      inclMat h (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :=
  rfl

theorem inclGL_mem (A : StatedSp 2 h.fixedField) :
    inclGL h (A : GL (Fin 2 ⊕ Fin 2) h.fixedField) ∈ hypSU h 2 0 := by
  rw [mem_gramSU, coe_inclGL]
  exact inclMat_mem h A

@[expose] noncomputable def spIncl : StatedSp 2 h.fixedField →* hypSU h 2 0 where
  toFun A := ⟨inclGL h (A : GL (Fin 2 ⊕ Fin 2) h.fixedField), inclGL_mem h A⟩
  map_one' := by
    apply hypSU_ext h
    change inclMat h ((1 : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) = 1
    rw [Units.val_one, inclMat_one]
  map_mul' A B := by
    apply hypSU_ext h
    change inclMat h (((A * B : StatedSp 2 h.fixedField) : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) =
      inclMat h ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) *
      inclMat h ((B : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)
    rw [Subgroup.coe_mul, Units.val_mul, inclMat_mul]

theorem coe_spIncl (A : StatedSp 2 h.fixedField) :
    (((spIncl h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      inclMat h ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) :=
  rfl

theorem spIncl_injective : Function.Injective (spIncl h) := by
  intro A B e
  have e1 := congrArg (fun g : hypSU h 2 0 => ((g : GL Ix K) : Matrix Ix Ix K)) e
  simp only [coe_spIncl] at e1
  exact Subtype.ext (Units.ext (inclMat_injective h e1))

theorem range_spIncl : (spIncl h).range = frobFix h := by
  have := charP_fixedField h
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    apply hypSU_ext h
    rw [coe_frobElt, coe_spIncl, inclMat_bar]
  · intro g hg
    have hfix : ∀ i j : Ix, (((g : GL Ix K) : Matrix Ix Ix K) i j) ∈ h.fixedField := fun i j => by
      rw [h.mem_fixedField]
      have := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K) i j) hg
      simpa [frobElt_apply] using this
    have hfix' : ∀ i j : Ix, ((((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j) ∈
        h.fixedField := fun i j => by
      rw [h.mem_fixedField]
      have hg' : g⁻¹ ∈ frobFix h := (frobFix h).inv_mem hg
      have := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K) i j) hg'
      simpa [frobElt_apply] using this
    let A₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField :=
      Matrix.of fun a b => ⟨_, hfix (ixEF.symm a) (ixEF.symm b)⟩
    let B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField :=
      Matrix.of fun a b => ⟨_, hfix' (ixEF.symm a) (ixEF.symm b)⟩
    have hA₀ : inclMat h A₀ = ((g : GL Ix K) : Matrix Ix Ix K) := by
      ext i j
      simp [inclMat_apply, A₀]
    have hB₀ : inclMat h B₀ = (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) := by
      ext i j
      simp [inclMat_apply, B₀]
    have hAB : A₀ * B₀ = 1 := by
      apply inclMat_injective h
      rw [inclMat_mul, hA₀, hB₀, inclMat_one, ← coe_mul_hypSU, mul_inv_cancel]
      rfl
    have hBA : B₀ * A₀ = 1 := by
      apply inclMat_injective h
      rw [inclMat_mul, hA₀, hB₀, inclMat_one, ← coe_mul_hypSU, inv_mul_cancel]
      rfl
    let A : GL (Fin 2 ⊕ Fin 2) h.fixedField := ⟨A₀, B₀, hAB, hBA⟩
    have hAsp : A ∈ StatedSp 2 h.fixedField := by
      apply Subgroup.subset_closure
      change A₀ᵀ * spJ h.fixedField * A₀ = spJ h.fixedField
      apply inclMat_injective h
      rw [inclMat_mul, inclMat_mul, ← inclMat_transpose, ← hypGram_eq_inclMat h, hA₀]
      have hgram := (mem_gramSU.mp g.2).1
      have hbar : ((g : GL Ix K) : Matrix Ix Ix K).map h.bar =
          ((g : GL Ix K) : Matrix Ix Ix K) := by
        rw [← hA₀, inclMat_bar]
      rwa [hbar] at hgram
    refine ⟨⟨A, hAsp⟩, hypSU_ext h ?_⟩
    rw [coe_spIncl]
    exact hA₀

omit h in
theorem ixEF_ie1 : ixEF ie1 = (Sum.inl 0 : Fin 2 ⊕ Fin 2) := by decide

omit h in
theorem col_of_mem_Q2_zero {F : Type} [Field F] {A : StatedSp 2 F} (hA : A ∈ Q2 F 0)
    (b : Fin 2 ⊕ Fin 2) (hb : b ≠ Sum.inl 0) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) b (Sum.inl 0) = 0 := by
  have hmem : (Pi.single (Sum.inl 0) (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 1 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have : (j : Fin 2) ≠ 0 := fun h0 => by subst h0; simp at hj
    simp [this]
  have hA' : A ∈ stabilizer 2 F (flag 2 F 1) := hA
  rw [mem_stabilizer] at hA'
  have himg : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      Pi.single (Sum.inl 0) 1 ∈ flag 2 F 1 := by
    rw [← hA']
    exact ⟨_, hmem, rfl⟩
  rw [mem_flag_of_le (by norm_num), mem_isoFlag, mulVec_single_one] at himg
  rcases b with j | j
  · have hj : (j : ℕ) ≠ 0 := fun h0 => hb (by rw [show j = 0 from Fin.ext h0])
    exact himg.2 j (by omega)
  · exact himg.1 j

omit h in
theorem mem_Q2_zero_of_col {F : Type} [Field F] {A : StatedSp 2 F}
    (hA : ∀ b, b ≠ Sum.inl 0 →
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) b (Sum.inl 0) = 0)
    (hA' : ∀ b, b ≠ Sum.inl 0 →
      (((A⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        b (Sum.inl 0) = 0) :
    A ∈ Q2 F 0 := by
  have key : ∀ (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      (∀ b, b ≠ Sum.inl 0 → M b (Sum.inl 0) = 0) →
      ∀ v ∈ flag 2 F 1, M *ᵥ v ∈ flag 2 F 1 := by
    intro M hM v hv
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hv ⊢
    have hvs : v = Pi.single (Sum.inl 0) (v (Sum.inl 0)) := by
      funext c
      rcases c with j | j
      · by_cases hj : j = 0
        · subst hj
          simp
        · have : (1 : ℕ) ≤ j := by
            rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h0 | h1
            · exact absurd h0 hj
            · rw [h1]; simp
          rw [hv.2 j this]
          simp [hj]
      · rw [hv.1 j]
        simp
    rw [hvs, mulVec_single]
    refine ⟨fun j => by simp [hM (Sum.inr j) (by simp)], fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h0 => by subst h0; simp at hj
    simp [hM (Sum.inl j) (by simpa using hj0)]
  exact mem_stabilizer_of_mulVec_mem (key _ hA) (key _ hA')

theorem spIncl_mem_parP_iff (A : StatedSp 2 h.fixedField) :
    spIncl h A ∈ parP h ↔ ∀ b, b ≠ Sum.inl 0 →
      ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)
        b (Sum.inl 0) = 0 := by
  rw [mem_parP_iff]
  constructor
  · intro hP b hb
    have := hP (ixEF.symm b) (fun e => hb (by rw [← ixEF_ie1, ← e, Equiv.apply_symm_apply]))
    rw [coe_spIncl, inclMat_apply, Equiv.apply_symm_apply, ixEF_ie1] at this
    exact Subtype.ext this
  · intro hc a ha
    rw [coe_spIncl, inclMat_apply, ixEF_ie1,
      hc (ixEF a) (fun e => ha (ixEF.injective (e.trans ixEF_ie1.symm)))]
    rfl

theorem map_spIncl_Q2 : (Q2 h.fixedField 0).map (spIncl h) = parP h ⊓ frobFix h := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨(spIncl_mem_parP_iff h A).mpr (col_of_mem_Q2_zero hA),
      range_spIncl h ▸ ⟨A, rfl⟩⟩
  · rintro g ⟨hgP, hgF⟩
    rw [← range_spIncl h] at hgF
    obtain ⟨A, rfl⟩ := hgF
    refine ⟨A, mem_Q2_zero_of_col ((spIncl_mem_parP_iff h A).mp hgP) ?_, rfl⟩
    have hinv : spIncl h A⁻¹ ∈ parP h := by
      rw [map_inv]
      exact (parP h).inv_mem hgP
    exact (spIncl_mem_parP_iff h A⁻¹).mp hinv

omit h in
theorem isMaxParabolic2_Q2_zero (F : Type) [Field F] [Finite F] [CharP F 2] :
    IsMaxParabolic2 (⊤ : Subgroup (StatedSp 2 F)) (Q2 F 0) := by
  have hNU : Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) = borelSubgroup 2 F :=
    SymplecticHigher.normalizer_unipotent
  have hUB : unipotent 2 F ≤ borelSubgroup 2 F := hNU ▸ Subgroup.le_normalizer
  have hB0 : borelSubgroup 2 F ≤ Q2 F 0 := Vol2Native.A312L.borelSubgroup_le_Q2 0
  have hw1 : weylRep F 1 ∈ Q2 F 0 := by
    rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by decide)]
    decide
  have hw1' : weylRep F 1 ∉ Q2 F 1 := by
    rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by decide)]
    decide
  have hw0 : weylRep F 0 ∉ Q2 F 0 := by
    rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by decide)]
    decide
  refine ⟨⟨le_top, unipotent 2 F, SzN2.isSylowTwoOf_unipotent, ?_⟩, ?_, ?_⟩
  · rw [top_inf_eq, hNU]
    exact hB0
  · intro htop
    exact hw0 (htop ▸ Subgroup.mem_top _)
  · intro Q' _ hQ't hle
    rcases contained_in_Q2 (hUB.trans (hB0.trans hle)) hQ't with h0 | h1
    · exact le_antisymm h0 hle
    · exact absurd (h1 (hle hw1)) hw1'

theorem sAdm_of_fixed {x y c : K} (hx : h.bar x = x) (hy : h.bar y = y) (hc : h.bar c = c) :
    SAdm h x y c := by
  have := h.charP
  unfold SAdm
  rw [hx, hy, hc, CharTwo.add_self_eq_zero, mul_comm y x, CharTwo.add_self_eq_zero]

theorem coe_comm_levHom {s : hypSU h 2 0} {x y c : K} (hcF : h.bar c = c) (hc : SAdm h x y c)
    (hs : ((s : GL Ix K) : Matrix Ix Ix K) = sMat h x y c)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (((s * levHom h A * s⁻¹ * (levHom h A)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (x + (slMat h A 0 0 * x + slMat h A 0 1 * y))
        (y + (slMat h A 1 0 * x + slMat h A 1 1 * y))
        (h.bar y * (slMat h A 0 0 * x + slMat h A 0 1 * y) +
          h.bar x * (slMat h A 1 0 * x + slMat h A 1 1 * y)) := by
  have := h.charP
  have hsi : (((s⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y c := by
    rw [coe_inv_of_sMat hc hs, hcF]
  have e : s * levHom h A * s⁻¹ * (levHom h A)⁻¹ = s * (levHom h A * s⁻¹ * (levHom h A)⁻¹) := by
    group
  rw [e, coe_mul_hypSU, coe_conj_levHom h hsi A, hs, sMat_mul, CharTwo.add_self_eq_zero, zero_add]

theorem radQ_inf_frobFix_le (hm : 2 ≤ m) :
    radQ h ⊓ frobFix h ≤ perfectCore (parP h ⊓ frobFix h) := by
  classical
  have := h.charP
  have := h.finite
  have := finite_hypSU h
  have := charP_fixedField h
  set Pc := perfectCore (parP h ⊓ frobFix h) with hPc
  have hlev : (levHom h).range ≤ Pc := by
    refine le_perfectCore_of_perfect (fun g hg => Subgroup.mem_inf.mpr ⟨levHom_le_parP h hg, ?_⟩) ?_
    · obtain ⟨A, rfl⟩ := hg
      exact frobElt_levHom h A
    · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_sl2_eq_top h hm]
  have hnorm : parP h ⊓ frobFix h ≤ Subgroup.normalizer (Pc : Set (hypSU h 2 0)) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  let PiC : K → K → K → Prop := fun x y c =>
    ∃ g ∈ Pc, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c
  have hmul : ∀ {x y c x' y' c'}, PiC x y c → PiC x' y' c' →
      PiC (x + x') (y + y') (c + c' + (h.bar y * x' + h.bar x * y')) := by
    rintro x y c x' y' c' ⟨g, hg, hgc⟩ ⟨g', hg', hgc'⟩
    exact ⟨g * g', Pc.mul_mem hg hg', by rw [coe_mul_hypSU, hgc, hgc', sMat_mul]⟩
  have hfix : ∀ a : h.fixedField, h.bar (a : K) = a := fun a => (h.mem_fixedField).mp a.2
  have hcomm : ∀ {x y c : K}, h.bar x = x → h.bar y = y → h.bar c = c →
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField,
        PiC (x + (slMat h A 0 0 * x + slMat h A 0 1 * y))
          (y + (slMat h A 1 0 * x + slMat h A 1 1 * y))
          (h.bar y * (slMat h A 0 0 * x + slMat h A 0 1 * y) +
            h.bar x * (slMat h A 1 0 * x + slMat h A 1 1 * y)) := by
    intro x y c hx hy hc A
    have hadm := sAdm_of_fixed h hx hy hc
    set s := sElt h hadm with hsdef
    have hsP : s ∈ parP h ⊓ frobFix h := by
      refine ⟨radQ_le_parP h (sElt_mem_radQ h hadm), ?_⟩
      apply hypSU_ext h
      rw [coe_frobElt, coe_sElt]
      ext i j
      rcases ix_cases i with rfl | rfl | rfl | rfl <;>
        rcases ix_cases j with rfl | rfl | rfl | rfl <;>
        simp [map_apply, sMat_apply, one_apply, ie1, ie2, if1, if2, hx, hy, hc]
    have hl : levHom h A ∈ Pc := hlev ⟨A, rfl⟩
    have hmem : s * levHom h A * s⁻¹ * (levHom h A)⁻¹ ∈ Pc :=
      Pc.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnorm hsP) _).mp hl) (Pc.inv_mem hl)
    exact ⟨_, hmem, coe_comm_levHom h hc hadm (coe_sElt h hadm) A⟩
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcongr : ∀ {x y c x' y' c' : K}, PiC x y c → x = x' → y = y' → c = c' → PiC x' y' c' := by
    rintro x y c x' y' c' hP rfl rfl rfl
    exact hP
  have h1 : ∀ t w : h.fixedField, PiC ((t : K) * w) 0 ((t : K) * w * w) := by
    intro t w
    have := hcomm (x := 0) (y := (w : K)) (c := 0) (map_zero _) (hfix w) (map_zero _) (slUt h t)
    refine hcongr this ?_ ?_ ?_
    all_goals (try simp [slMat, slUt, hfix])
    all_goals (try ring_nf)
    all_goals (try simp [h2K])
  have h2 : ∀ t : h.fixedField, PiC 0 (t : K) (t : K) := by
    intro t
    have := hcomm (x := 1) (y := 0) (c := 0) (map_one _) (map_zero _) (map_zero _) (slLt h t)
    refine hcongr this ?_ ?_ ?_
    all_goals (try simp [slMat, slLt])
    all_goals (try ring_nf)
    all_goals (try simp [h2K])
  obtain ⟨w₀, hw0, hw1⟩ : ∃ w₀ : h.fixedField, w₀ ≠ 0 ∧ w₀ ≠ 1 := by
    have : Fintype h.fixedField := Fintype.ofFinite _
    have hcard : 4 ≤ Fintype.card h.fixedField := by
      rw [← Nat.card_eq_fintype_card, h.card_fixedField]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (Finset.univ : Finset h.fixedField) ⊆ {0, 1} := fun a _ => by
      by_cases ha : a = 0
      · simp [ha]
      · simp [hall a ha]
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h3
    have h4 : ({0, 1} : Finset h.fixedField).card ≤ 2 := Finset.card_le_two
    omega
  have hw0K : (w₀ : K) ≠ 0 := fun e => hw0 (Subtype.ext e)
  have hw1K : (w₀ : K) + 1 ≠ 0 := by
    intro e
    apply hw1
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    linear_combination e - h2K
  have h3 : ∀ c : h.fixedField, PiC 0 0 (c : K) := by
    intro c
    have hden : (w₀ : K) * ((w₀ : K) + 1) ≠ 0 := mul_ne_zero hw0K hw1K
    set t : h.fixedField := c * (w₀ * (w₀ + 1))⁻¹ with ht
    have htK : (t : K) * ((w₀ : K) * ((w₀ : K) + 1)) = c := by
      simp only [ht, Subfield.coe_mul, Subfield.coe_inv, Subfield.coe_add, OneMemClass.coe_one]
      field_simp
    have hAB := hmul (h1 t w₀) (h1 (t * w₀) 1)
    refine hcongr hAB ?_ ?_ ?_
    · simp only [Subfield.coe_mul, OneMemClass.coe_one, mul_one]
      linear_combination ((t : K) * w₀) * h2K
    · simp
    · simp only [Subfield.coe_mul, OneMemClass.coe_one, mul_one, map_zero, zero_mul, mul_zero,
        add_zero]
      linear_combination htK
  have h4 : ∀ u : h.fixedField, PiC (u : K) 0 0 := by
    intro u
    have := hmul (h1 u 1) (h3 u)
    refine hcongr this ?_ ?_ ?_
    all_goals (try simp)
    all_goals (try ring_nf)
    all_goals (try simp [h2K])
  have h5 : ∀ v : h.fixedField, PiC 0 (v : K) 0 := by
    intro v
    have := hmul (h2 v) (h3 v)
    refine hcongr this ?_ ?_ ?_
    all_goals (try simp)
    all_goals (try ring_nf)
    all_goals (try simp [h2K])
  have h6 : ∀ x y c : h.fixedField, PiC (x : K) (y : K) (c : K) := by
    intro x y c
    have hxy := hmul (h4 x) (h5 y)
    have := hmul hxy (h3 (c + x * y))
    refine hcongr this ?_ ?_ ?_
    all_goals (try simp [hfix])
    all_goals (try ring_nf)
    all_goals (try simp [h2K])
  rintro g ⟨hgQ, hgF⟩
  obtain ⟨x, y, c, hc, hG⟩ := hgQ
  have hbar : ∀ i j, h.bar ((((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j) =
      (((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j := fun i j => by
    have := congrArg (fun z : hypSU h 2 0 => ((z : GL Ix K) : Matrix Ix Ix K) i j) hgF
    simpa [frobElt_apply] using this
  have hx : h.bar x = x := by have := hbar ie2 if1; rwa [hG, sMat_ie2_if1] at this
  have hy : h.bar y = y := by have := hbar if2 if1; rwa [hG, sMat_if2_if1] at this
  have hcc : h.bar c = c := by have := hbar ie1 if1; rwa [hG, sMat_ie1_if1] at this
  obtain ⟨g', hg', hg'c⟩ := h6 ⟨x, (h.mem_fixedField).mpr hx⟩ ⟨y, (h.mem_fixedField).mpr hy⟩
    ⟨c, (h.mem_fixedField).mpr hcc⟩
  have e : g' = g := hypSU_ext h (by rw [hg'c, hG])
  exact e ▸ hg'

theorem perfectCore_inf_frobFix (hm : 2 ≤ m) :
    perfectCore (parP h ⊓ frobFix h) = perfectCore (parP h) ⊓ frobFix h := by
  have := h.finite
  have := finite_hypSU h
  apply le_antisymm
  · exact le_inf (perfectCore_mono inf_le_left) ((perfectCore_le _).trans inf_le_right)
  · rintro l ⟨hl, hlF⟩
    have hN : (levHom h).range ≤ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)) :=
      (levHom_le_parP h).trans (parP_le_normalizer_radQ h)
    obtain ⟨s, hs, _, ⟨A, rfl⟩, rfl⟩ :=
      exists_mul_eq_of_mem_sup_of_le_normalizer hN
        (parH_le_radQ_sup h (perfectCore_parP_le_parH h hl))
    have hsF : s ∈ frobFix h := by
      have e := (mem_frobFix h).mp hlF
      rw [← frob_apply, map_mul, frob_apply, frob_apply, frobElt_levHom] at e
      exact mul_right_cancel e
    have hlev : levHom h A ∈ perfectCore (parP h ⊓ frobFix h) := by
      refine le_perfectCore_of_perfect
        (fun g hg => Subgroup.mem_inf.mpr ⟨levHom_le_parP h hg, ?_⟩) ?_ ⟨A, rfl⟩
      · obtain ⟨B, rfl⟩ := hg
        exact frobElt_levHom h B
      · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_sl2_eq_top h hm]
    exact (perfectCore _).mul_mem (radQ_inf_frobFix_le h hm (Subgroup.mem_inf.mpr ⟨hs, hsF⟩)) hlev

theorem exists_sp4_parabolic_equiv (hm : 2 ≤ m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      ∃ P : Subgroup ↥(StatedSp 2 F), IsMaxParabolic2 ⊤ P ∧
        Nonempty (↥(perfectCore (parP h) ⊓ frobFix h) ≃* ↥(perfectCore P)) := by
  have := h.finite
  have := finite_hypSU h
  have := charP_fixedField h
  have hfin : Finite (StatedSp 2 h.fixedField) := inferInstance
  refine ⟨h.fixedField, inferInstance, inferInstance, h.card_fixedField, Q2 h.fixedField 0,
    isMaxParabolic2_Q2_zero h.fixedField, ?_⟩
  have e1 : (perfectCore (Q2 h.fixedField 0)).map (spIncl h) =
      perfectCore (parP h) ⊓ frobFix h := by
    rw [map_perfectCore, map_spIncl_Q2, perfectCore_inf_frobFix h hm]
  exact ⟨(MulEquiv.subgroupCongr e1.symm).trans
    ((perfectCore (Q2 h.fixedField 0)).equivMapOfInjective _ (spIncl_injective h)).symm⟩

end CFSG.Quasithin.H13.U4Par
