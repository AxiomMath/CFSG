module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private abbrev caPara_Mat1 (m : ℕ) : Type := Matrix (Fin 1) (Fin m) (ZMod 2)

private abbrev caPara_MatC : Type := Matrix (Fin 1) (Fin 1) (ZMod 2)

private abbrev caPara_Pair (m : ℕ) : Type := caPara_Mat1 m × caPara_MatC

private noncomputable def caPara_uOneAddHom (m : ℕ) :
    caPara_Pair m →+ Additive ↥(uOne m) where
  toFun x := Additive.ofMul ⟨uGL x.1 0 x.2, ⟨x.1, x.2, rfl⟩⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [uGL_zero]
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using (uGL_mul x.1 y.1 0 0 x.2 y.2).symm

private noncomputable def caPara_uOneAddEquiv (m : ℕ) :
    caPara_Pair m ≃+ Additive ↥(uOne m) :=
  AddEquiv.ofBijective (caPara_uOneAddHom m)
    (by
      constructor
      · intro x y h
        have h' : (uGL x.1 0 x.2 : GL (BlkIdx 1 m) (ZMod 2)) = uGL y.1 0 y.2 := by
          have := congrArg (fun z : Additive ↥(uOne m) =>
            (z.toMul : GL (BlkIdx 1 m) (ZMod 2))) h
          simpa [caPara_uOneAddHom] using this
        obtain ⟨h1, -, h2⟩ := uGL_injective h'
        exact Prod.ext h1 h2
      · intro u
        obtain ⟨a, c, h⟩ := u.2
        refine ⟨(a, c), ?_⟩
        apply Additive.toMul.injective
        apply Subtype.ext
        change (uGL a 0 c : GL (BlkIdx 1 m) (ZMod 2)) =
          ((Additive.toMul u : ↥(uOne m)) : GL (BlkIdx 1 m) (ZMod 2))
        exact h.symm)

private theorem caPara_uOneAddEquiv_apply (m : ℕ) (x : caPara_Pair m) :
    ((caPara_uOneAddEquiv m x).toMul : GL (BlkIdx 1 m) (ZMod 2)) = uGL x.1 0 x.2 := by
  change ((Additive.toMul ((caPara_uOneAddHom m) x) : ↥(uOne m)) :
    GL (BlkIdx 1 m) (ZMod 2)) = uGL x.1 0 x.2
  rfl

private theorem caPara_toAdditive_ofMul {G H : Type*} [Group G] [Group H] (f : G ≃* H)
    (g : G) : f.toAdditive (Additive.ofMul g) = Additive.ofMul (f g) := rfl

private noncomputable def caPara_rowEquiv (ι : Type*) [Fintype ι] :
    Matrix (Fin 1) ι (ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) where
  toFun a := fun j => a 0 j
  invFun v := Matrix.of fun _ j => v j
  left_inv a := by
    ext i j
    fin_cases i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def caPara_transposeGL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : GL ι (ZMod 2)) : GL ι (ZMod 2) :=
  ⟨(S : Matrix ι ι (ZMod 2))ᵀ, ((S⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))ᵀ, by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

private noncomputable def caPara_glEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    GL ι (ZMod 2) ≃* ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :=
  (Matrix.GeneralLinearGroup.toLin (n := ι) (R := ZMod 2)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2))

private noncomputable def caPara_glOfLinearEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) : GL ι (ZMod 2) :=
  (caPara_glEquiv ι).symm φ

private theorem caPara_glEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : GL ι (ZMod 2)) (v : ι → ZMod 2) :
    caPara_glEquiv ι S v = (S : Matrix ι ι (ZMod 2)) *ᵥ v := by
  rw [caPara_glEquiv, MulEquiv.trans_apply]
  change (↑(Matrix.GeneralLinearGroup.toLin S) : (ι → ZMod 2) → (ι → ZMod 2)) v =
    (S : Matrix ι ι (ZMod 2)) *ᵥ v
  rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

private theorem caPara_glOfLinearEquiv_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (v : ι → ZMod 2) :
    (caPara_glOfLinearEquiv φ : Matrix ι ι (ZMod 2)) *ᵥ v = φ v := by
  have h : caPara_glEquiv ι (caPara_glOfLinearEquiv φ) = φ :=
    (caPara_glEquiv ι).apply_symm_apply φ
  calc (caPara_glOfLinearEquiv φ : Matrix ι ι (ZMod 2)) *ᵥ v
      = caPara_glEquiv ι (caPara_glOfLinearEquiv φ) v :=
        (caPara_glEquiv_apply _ _).symm
    _ = φ v := congrArg (fun e : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) => e v) h

private theorem caPara_rowEquiv_mul_transpose {ι : Type*} [Fintype ι]
    (v : Matrix (Fin 1) ι (ZMod 2)) (S : Matrix ι ι (ZMod 2)) :
    caPara_rowEquiv ι (v * Sᵀ) = S *ᵥ caPara_rowEquiv ι v := by
  funext j
  show (∑ i, v 0 i * S j i) = ∑ i, S j i * v 0 i
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private noncomputable def caPara_rowColEquiv {ι : Type*} [Fintype ι]
    (φ : Matrix (Fin 1) ι (ZMod 2) ≃ₗ[ZMod 2] Matrix (Fin 1) ι (ZMod 2)) :
    (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
  (caPara_rowEquiv ι).symm.trans (φ.trans (caPara_rowEquiv ι))

private theorem caPara_row_apply_eq_mul_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Matrix (Fin 1) ι (ZMod 2) ≃ₗ[ZMod 2] Matrix (Fin 1) ι (ZMod 2))
    (v : Matrix (Fin 1) ι (ZMod 2)) :
    v * ((caPara_glOfLinearEquiv (caPara_rowColEquiv φ) : GL ι (ZMod 2)) :
        Matrix ι ι (ZMod 2))ᵀ = φ v := by
  apply (caPara_rowEquiv ι).injective
  rw [caPara_rowEquiv_mul_transpose, caPara_glOfLinearEquiv_mulVec, caPara_rowColEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

private def caPara_rowOf {m : ℕ} (a : caPara_Mat1 m) (c : caPara_MatC) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) :=
  Matrix.of fun i j => Sum.elim (fun b => a i b) (fun c' => c i c') j

private def caPara_rowFst {m : ℕ} (φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    caPara_Mat1 m := fun i j => φ i (Sum.inl j)

private def caPara_rowSnd {m : ℕ} (φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    caPara_MatC := fun i j => φ i (Sum.inr j)

private theorem caPara_rowOf_fst_snd {m : ℕ}
    (φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    caPara_rowOf (caPara_rowFst φ) (caPara_rowSnd φ) = φ := by
  ext i j
  rcases j with b | c <;> rfl

private noncomputable def caPara_pairRowHom (m : ℕ) :
    caPara_Pair m →+ Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) where
  toFun x := caPara_rowOf x.1 x.2
  map_zero' := by
    ext i j
    rcases j with b | c <;> rfl
  map_add' x y := by
    ext i j
    rcases j with b | c <;> rfl

private noncomputable def caPara_pairRowEquiv (m : ℕ) :
    caPara_Pair m ≃+ Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) :=
  AddEquiv.ofBijective (caPara_pairRowHom m)
    (by
      constructor
      · intro x y h
        have h1 : x.1 = y.1 := by
          ext i j
          have := congrFun₂ h i (Sum.inl j)
          simpa [caPara_pairRowHom, caPara_rowOf, Matrix.of_apply] using this
        have h2 : x.2 = y.2 := by
          ext i j
          have := congrFun₂ h i (Sum.inr j)
          simpa [caPara_pairRowHom, caPara_rowOf, Matrix.of_apply] using this
        exact Prod.ext h1 h2
      · intro v
        exact ⟨(caPara_rowFst v, caPara_rowSnd v), caPara_rowOf_fst_snd v⟩)

private theorem caPara_pairRowEquiv_symm_apply (m : ℕ)
    (φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    (caPara_pairRowEquiv m).symm φ = (caPara_rowFst φ, caPara_rowSnd φ) := by
  apply (caPara_pairRowEquiv m).injective
  rw [(caPara_pairRowEquiv m).apply_symm_apply]
  change φ = caPara_rowOf (caPara_rowFst φ) (caPara_rowSnd φ)
  exact (caPara_rowOf_fst_snd φ).symm

private noncomputable def caPara_uOneRowAddEquiv (m : ℕ) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) ≃+ Additive ↥(uOne m) :=
  (caPara_pairRowEquiv m).symm.trans (caPara_uOneAddEquiv m)

private theorem caPara_uOneRowAddEquiv_apply (m : ℕ)
    (φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    ((caPara_uOneRowAddEquiv m φ).toMul : GL (BlkIdx 1 m) (ZMod 2)) =
      uGL (caPara_rowFst φ) 0 (caPara_rowSnd φ) := by
  rw [caPara_uOneRowAddEquiv, AddEquiv.trans_apply, caPara_pairRowEquiv_symm_apply,
    caPara_uOneAddEquiv_apply]

private noncomputable def caPara_coordRow {m : ℕ} (u : ↥(uOne m)) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) :=
  (caPara_uOneRowAddEquiv m).symm (Additive.ofMul u)

private theorem caPara_coordRow_spec {m : ℕ} (u : ↥(uOne m)) :
    (u : GL (BlkIdx 1 m) (ZMod 2)) =
      uGL (caPara_rowFst (caPara_coordRow u)) 0 (caPara_rowSnd (caPara_coordRow u)) := by
  have h : caPara_uOneRowAddEquiv m (caPara_coordRow u) = Additive.ofMul u :=
    (caPara_uOneRowAddEquiv m).apply_symm_apply _
  have h2 : ((caPara_uOneRowAddEquiv m (caPara_coordRow u)).toMul :
      GL (BlkIdx 1 m) (ZMod 2)) = (u : GL (BlkIdx 1 m) (ZMod 2)) := by rw [h]; rfl
  rw [caPara_uOneRowAddEquiv_apply] at h2
  exact h2.symm

private noncomputable def caPara_Frow {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m)) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) ≃+
      Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) :=
  ((caPara_uOneRowAddEquiv m).trans (f.toAdditive)).trans (caPara_uOneRowAddEquiv m).symm

private theorem caPara_coordRow_f {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m))
    (u : ↥(uOne m)) :
    caPara_coordRow (f u) = caPara_Frow f (caPara_coordRow u) := by
  rw [caPara_coordRow, caPara_coordRow, caPara_Frow, AddEquiv.trans_apply,
    AddEquiv.trans_apply, (caPara_uOneRowAddEquiv m).apply_symm_apply,
    caPara_toAdditive_ofMul]

private noncomputable def caPara_FrowLinMap {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m)) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) →ₗ[ZMod 2]
      Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) where
  toFun := caPara_Frow f
  map_add' := (caPara_Frow f).map_add
  map_smul' r v := by
    have hr : r = 0 ∨ r = 1 := by
      have h : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
      exact h r
    rcases hr with rfl | rfl <;> simp

private noncomputable def caPara_FrowLinEquiv {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m)) :
    Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) ≃ₗ[ZMod 2]
      Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) :=
  LinearEquiv.ofBijective (caPara_FrowLinMap f)
    (by
      change Function.Bijective (caPara_Frow f)
      exact (caPara_Frow f).bijective)

private noncomputable def caPara_Srow {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m)) :
    GL (Fin m ⊕ Fin 1) (ZMod 2) :=
  caPara_glOfLinearEquiv (caPara_rowColEquiv (caPara_FrowLinEquiv f))

private theorem caPara_Srow_row {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m))
    (v : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) :
    v * ((caPara_Srow f : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2))ᵀ = caPara_Frow f v := by
  rw [caPara_Srow, caPara_row_apply_eq_mul_transpose]
  change caPara_Frow f v = caPara_Frow f v
  rfl

private noncomputable def caPara_blockGL (m : ℕ)
    (h : GL (Fin m ⊕ Fin 1) (ZMod 2)) : GL (BlkIdx 1 m) (ZMod 2) where
  val := Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
    (h : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2))
  inv := Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
    ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1)
      (ZMod 2))
  val_inv := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul]
  inv_val := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul]

private theorem caPara_uGL_eq_one_add_fromBlocks (m : ℕ) (a : caPara_Mat1 m)
    (c : caPara_MatC) :
    (uGL a 0 c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) (caPara_rowOf a c)
        0 (0 : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [uGL, uMat, blk, caPara_rowOf, Matrix.fromBlocks, Matrix.one_apply]

private theorem caPara_blockGL_uGL_conj (m : ℕ) (h : GL (Fin m ⊕ Fin 1) (ZMod 2))
    (a : caPara_Mat1 m) (c : caPara_MatC) :
    caPara_blockGL m h * uGL a 0 c * (caPara_blockGL m h)⁻¹ =
      uGL (caPara_rowFst (caPara_rowOf a c *
          ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2))))
        0 (caPara_rowSnd (caPara_rowOf a c *
          ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)))) := by
  apply Units.ext
  simp only [Units.val_mul]
  have hy : (caPara_blockGL m h : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
        (h : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) := rfl
  have hyi : (↑((caPara_blockGL m h)⁻¹) : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
        ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) := rfl
  rw [hy, hyi, caPara_uGL_eq_one_add_fromBlocks, caPara_uGL_eq_one_add_fromBlocks,
    caPara_rowOf_fst_snd]
  have hyy : Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
      (h : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) *
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
        ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul]
  have hN : Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
      (h : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) *
      Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) (caPara_rowOf a c) 0
        (0 : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) *
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) 0 0
        ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) =
      Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) (ZMod 2))
        (caPara_rowOf a c * ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2))) 0
        (0 : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one]
  conv_lhs => rw [mul_add, mul_one, add_mul]
  rw [hyy, hN]

private theorem caPara_blockGL_mem_uOne (m : ℕ) (h : GL (Fin m ⊕ Fin 1) (ZMod 2))
    {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uOne m) :
    caPara_blockGL m h * u * (caPara_blockGL m h)⁻¹ ∈ uOne m := by
  obtain ⟨a, c, rfl⟩ := hu
  rw [caPara_blockGL_uGL_conj]
  exact ⟨_, _, rfl⟩

private theorem caPara_blockGL_mem_normalizer (m : ℕ) (h : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
    caPara_blockGL m h ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨caPara_blockGL_mem_uOne m h, ?_⟩
  intro hu
  have hh : caPara_blockGL m h⁻¹ = (caPara_blockGL m h)⁻¹ := rfl
  have hmem := caPara_blockGL_mem_uOne m h⁻¹ hu
  rw [hh] at hmem
  have heq : (caPara_blockGL m h)⁻¹ * (caPara_blockGL m h * u * (caPara_blockGL m h)⁻¹) *
      ((caPara_blockGL m h)⁻¹)⁻¹ = u := by group
  rwa [heq] at hmem

theorem exists_normalizer_uOne_of_mulEquiv {m : ℕ} (f : ↥(uOne m) ≃* ↥(uOne m)) :
    ∃ y ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))),
      ∀ u : ↥(uOne m), ((f u : ↥(uOne m)) : GL (BlkIdx 1 m) (ZMod 2)) =
        y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹ := by
  let S : GL (Fin m ⊕ Fin 1) (ZMod 2) := caPara_Srow f
  let h : GL (Fin m ⊕ Fin 1) (ZMod 2) := (caPara_transposeGL S)⁻¹
  have hhm : ((h⁻¹ : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2)) =
      ((S : GL (Fin m ⊕ Fin 1) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (ZMod 2))ᵀ := by
    simp [h, caPara_transposeGL, inv_inv]
  let y : GL (BlkIdx 1 m) (ZMod 2) := caPara_blockGL m h
  refine ⟨y, caPara_blockGL_mem_normalizer m h, ?_⟩
  intro u
  let φ : Matrix (Fin 1) (Fin m ⊕ Fin 1) (ZMod 2) := caPara_coordRow u
  have hu : (u : GL (BlkIdx 1 m) (ZMod 2)) =
      uGL (caPara_rowFst φ) 0 (caPara_rowSnd φ) := caPara_coordRow_spec u
  have hfu : ((f u : ↥(uOne m)) : GL (BlkIdx 1 m) (ZMod 2)) =
      uGL (caPara_rowFst (caPara_Frow f φ)) 0 (caPara_rowSnd (caPara_Frow f φ)) := by
    have hc : caPara_coordRow (f u) = caPara_Frow f φ := caPara_coordRow_f f u
    rw [caPara_coordRow_spec (f u), hc]
  have hstep : y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹ =
      uGL (caPara_rowFst (caPara_Frow f φ)) 0 (caPara_rowSnd (caPara_Frow f φ)) := by
    have hconj := caPara_blockGL_uGL_conj m h (caPara_rowFst φ) (caPara_rowSnd φ)
    rw [caPara_rowOf_fst_snd] at hconj
    rw [← hu] at hconj
    rw [hhm, caPara_Srow_row] at hconj
    exact hconj
  rw [hfu]
  exact hstep.symm

private noncomputable def caPara_sigmaUOneToUTwo (m : ℕ) : ↥(uOne m) ≃* ↥(uTwo m) where
  toFun u := ⟨sigmaStd m (u : GL (BlkIdx 1 m) (ZMod 2)), by
    rw [← sigmaStd_map_uOne]
    exact ⟨u, u.2, rfl⟩⟩
  invFun v := ⟨sigmaStd m (v : GL (BlkIdx 1 m) (ZMod 2)), by
    rw [← sigmaStd_map_uTwo]
    exact ⟨v, v.2, rfl⟩⟩
  left_inv u := by
    apply Subtype.ext
    exact sigmaStd_sigmaStd m (u : GL (BlkIdx 1 m) (ZMod 2))
  right_inv v := by
    apply Subtype.ext
    exact sigmaStd_sigmaStd m (v : GL (BlkIdx 1 m) (ZMod 2))
  map_mul' u v := by
    apply Subtype.ext
    exact (sigmaStd m).map_mul (u : GL (BlkIdx 1 m) (ZMod 2))
      (v : GL (BlkIdx 1 m) (ZMod 2))

private theorem caPara_sigma_conj (m : ℕ) (y u : GL (BlkIdx 1 m) (ZMod 2)) :
    sigmaStd m y * sigmaStd m u * (sigmaStd m y)⁻¹ =
      sigmaStd m (y * u * y⁻¹) := by
  rw [← (sigmaStd m).map_inv, ← (sigmaStd m).map_mul, ← (sigmaStd m).map_mul]

private theorem caPara_sigma_conj_mem_uTwo (m : ℕ) {y : GL (BlkIdx 1 m) (ZMod 2)}
    (hy : y ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))))
    {w : GL (BlkIdx 1 m) (ZMod 2)} (hw : w ∈ uTwo m) :
    sigmaStd m y * w * (sigmaStd m y)⁻¹ ∈ uTwo m := by
  have hw' : w ∈ (uOne m).map (sigmaStd m).toMonoidHom := by
    rwa [sigmaStd_map_uOne]
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw'
  change sigmaStd m y * sigmaStd m u * (sigmaStd m y)⁻¹ ∈ uTwo m
  rw [caPara_sigma_conj]
  rw [← sigmaStd_map_uOne]
  exact ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy u).mp hu, rfl⟩

private theorem caPara_sigma_mem_normalizer (m : ℕ) {y : GL (BlkIdx 1 m) (ZMod 2)}
    (hy : y ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2)))) :
    sigmaStd m y ∈ Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨caPara_sigma_conj_mem_uTwo m hy, ?_⟩
  intro hv
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) :=
    (Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2)))).inv_mem hy
  have hmem := caPara_sigma_conj_mem_uTwo m (y := y⁻¹) hyinv
    (w := sigmaStd m y * v * (sigmaStd m y)⁻¹) hv
  have heq : sigmaStd m (y⁻¹) * (sigmaStd m y * v * (sigmaStd m y)⁻¹) *
      (sigmaStd m (y⁻¹))⁻¹ = v := by
    rw [(sigmaStd m).map_inv y]
    group
  rwa [heq] at hmem

theorem exists_normalizer_uTwo_of_mulEquiv {m : ℕ} (f : ↥(uTwo m) ≃* ↥(uTwo m)) :
    ∃ y ∈ Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))),
      ∀ u : ↥(uTwo m), ((f u : ↥(uTwo m)) : GL (BlkIdx 1 m) (ZMod 2)) =
        y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹ := by
  let σ : ↥(uOne m) ≃* ↥(uTwo m) := caPara_sigmaUOneToUTwo m
  let f₁ : ↥(uOne m) ≃* ↥(uOne m) := σ.trans (f.trans σ.symm)
  obtain ⟨y, hy, hconj⟩ := exists_normalizer_uOne_of_mulEquiv f₁
  let Y : GL (BlkIdx 1 m) (ZMod 2) := sigmaStd m y
  have hY : Y ∈ Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))) :=
    caPara_sigma_mem_normalizer m hy
  refine ⟨Y, hY, ?_⟩
  intro v
  let u : ↥(uOne m) := σ.symm v
  have hσu : σ u = v := σ.apply_symm_apply v
  have hfu : f₁ u = σ.symm (f v) := by
    change σ.symm (f (σ u)) = σ.symm (f v)
    rw [hσu]
  have hconj_u : (f₁ u : GL (BlkIdx 1 m) (ZMod 2)) =
      y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹ := hconj u
  have hYv : Y * (v : GL (BlkIdx 1 m) (ZMod 2)) * Y⁻¹ =
      (f v : GL (BlkIdx 1 m) (ZMod 2)) := by
    have h1 : Y * (v : GL (BlkIdx 1 m) (ZMod 2)) * Y⁻¹ =
        sigmaStd m (y * (u : GL (BlkIdx 1 m) (ZMod 2)) * y⁻¹) := by
      rw [← hσu]
      exact caPara_sigma_conj m y (u : GL (BlkIdx 1 m) (ZMod 2))
    rw [h1, ← hconj_u]
    rw [hfu]
    exact congrArg (fun z : ↥(uTwo m) => (z : GL (BlkIdx 1 m) (ZMod 2)))
      (σ.apply_symm_apply (f v))
  exact hYv.symm

end CFSG.StandardType.FF81.CentA

end
