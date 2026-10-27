module

public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.SeitzGeneration.RootPairSpBlock
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.LieType.SeitzGeneration.RootPairSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.StandardType.FieldTwoPSp

open Matrix
open CFSG.LieType.Steinberg (sl2Upper sl2Lower coe_sl2Upper coe_sl2Lower)
open CFSG.StandardType.RankOneXfer (sl2UpperUniSub mem_sl2UpperUniSub_iff)
open CFSG.StandardType.ClassicalPosition (matTransvGroup altSiegelGroup)
open CFSG.LieType.Universal (UniversalRootDatum)

section GramChart

variable {ι k F : Type} [Fintype ι] [DecidableEq ι] [Fintype k] [DecidableEq k] [CommRing F]

@[expose] def gramChart (M : Matrix ι k F) (N : Matrix k ι F) (X : Matrix k k F) :
    Matrix ι ι F :=
  1 + M * (X - 1) * N

omit [Fintype ι] in
theorem gramChart_one (M : Matrix ι k F) (N : Matrix k ι F) : gramChart M N 1 = 1 := by
  simp [gramChart]

theorem gramChart_mul {M : Matrix ι k F} {N : Matrix k ι F} (hNM : N * M = 1)
    (X Y : Matrix k k F) : gramChart M N (X * Y) = gramChart M N X * gramChart M N Y := by
  have h : M * (X - 1) * N * (M * (Y - 1) * N) = M * ((X - 1) * (Y - 1)) * N := by
    calc M * (X - 1) * N * (M * (Y - 1) * N)
        = M * (X - 1) * (N * M) * (Y - 1) * N := by simp only [Matrix.mul_assoc]
      _ = M * ((X - 1) * (Y - 1)) * N := by rw [hNM, Matrix.mul_one, Matrix.mul_assoc M]
  simp only [gramChart, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, h]
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  rw [hXY, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem gramChart_isometry {M : Matrix ι k F} {N : Matrix k ι F} {J : Matrix ι ι F}
    {G : Matrix k k F} (hNM : N * M = 1) (hJ : Jᵀ = J) (hMJ : Mᵀ * J = G * N) (hG : Gᵀ = G)
    {X : Matrix k k F} (hX : Xᵀ * G * X = G) :
    (gramChart M N X)ᵀ * J * gramChart M N X = J := by
  have hJM : J * M = Nᵀ * G := by
    have h := congrArg Matrix.transpose hMJ
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ, hG] at h
  set D := X - 1 with hD
  have key : G * D + Dᵀ * G + Dᵀ * G * D = 0 := by
    rw [hD, Matrix.transpose_sub, Matrix.transpose_one]
    have : G * (X - 1) + (Xᵀ - 1) * G + (Xᵀ - 1) * G * (X - 1) = Xᵀ * G * X - G := by
      noncomm_ring
    rw [this, hX, sub_self]
  have e1 : Nᵀ * Dᵀ * Mᵀ * J = Nᵀ * Dᵀ * G * N := by
    rw [Matrix.mul_assoc (Nᵀ * Dᵀ), hMJ, ← Matrix.mul_assoc]
  have e2 : J * (M * D * N) = Nᵀ * G * D * N := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJM]
  have e3 : Nᵀ * Dᵀ * Mᵀ * J * (M * D * N) = Nᵀ * Dᵀ * G * D * N := by
    rw [e1]
    calc Nᵀ * Dᵀ * G * N * (M * D * N) = Nᵀ * Dᵀ * G * (N * M) * D * N := by
          simp only [Matrix.mul_assoc]
      _ = Nᵀ * Dᵀ * G * D * N := by rw [hNM, Matrix.mul_one]
  have hT : (gramChart M N X)ᵀ = 1 + Nᵀ * Dᵀ * Mᵀ := by
    simp only [gramChart, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.mul_assoc, hD]
  rw [hT]
  change (1 + Nᵀ * Dᵀ * Mᵀ) * J * (1 + M * D * N) = J
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [e3, e2, e1]
  have h2 : Nᵀ * Dᵀ * G * N + (Nᵀ * G * D * N + Nᵀ * Dᵀ * G * D * N) =
      Nᵀ * (G * D + Dᵀ * G + Dᵀ * G * D) * N := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [add_assoc, h2, key, Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GramChart

section Form

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem J_transpose :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

omit [CharP F 2] in
theorem form_self (x : Fin n ⊕ Fin n → F) :
    x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x = 0 :=
  CFSG.ClassicalInvolution.Models.SymplecticPairs.form_self x

theorem sl2_transpose_swap (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A : Matrix (Fin 2) (Fin 2) F)ᵀ * !![0, 1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] := by
  have hneg : !![(0 : F), 1; 1, 0] = !![0, 1; -1, 0] := by rw [CharTwo.neg_eq]
  have key : ∀ B : Matrix (Fin 2) (Fin 2) F,
      Bᵀ * !![0, 1; -1, 0] * B = B.det • !![0, 1; -1, 0] := by
    intro B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
  rw [hneg, key, A.2, one_smul]

end Form

section ShortChart

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]

@[expose] def shortCol (a₁ a₂ b₁ b₂ : ι → F) : Fin 2 ⊕ Fin 2 → ι → F :=
  Sum.elim ![a₁, b₂] ![a₂, b₁]

@[expose] def shortRow (a₁ a₂ b₁ b₂ : ι → F) : Fin 2 ⊕ Fin 2 → ι → F :=
  Sum.elim ![b₁, a₂] ![b₂, a₁]

@[expose] def shortM (a₁ a₂ b₁ b₂ : ι → F) : Matrix ι (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun x i => shortCol a₁ a₂ b₁ b₂ i x

@[expose] def shortN (G : Matrix ι ι F) (a₁ a₂ b₁ b₂ : ι → F) : Matrix (Fin 2 ⊕ Fin 2) ι F :=
  Matrix.of fun i x => (G *ᵥ shortRow a₁ a₂ b₁ b₂ i) x

@[expose] def shortG : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks 0 !![0, 1; 1, 0] !![0, 1; 1, 0] 0

@[expose] def blk2 (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks A 0 0 A

omit [CharP F 2] in
theorem blk2_one : blk2 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := Matrix.fromBlocks_one

omit [CharP F 2] in
theorem blk2_mul (A B : Matrix (Fin 2) (Fin 2) F) : blk2 (A * B) = blk2 A * blk2 B := by
  simp [blk2, Matrix.fromBlocks_multiply]

omit [CharP F 2] in
theorem shortG_transpose : (shortG : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = shortG := by
  have hS : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp [shortG, Matrix.fromBlocks_transpose, hS]

theorem blk2_isometry (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (blk2 (A : Matrix (Fin 2) (Fin 2) F))ᵀ * shortG (F := F) * blk2 (A : Matrix (Fin 2) (Fin 2) F) =
      shortG := by
  simp only [blk2, shortG, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [sl2_transpose_swap]

variable {G : Matrix ι ι F} {a₁ a₂ b₁ b₂ : ι → F}

omit [DecidableEq ι] [CharP F 2] in
theorem formG_comm (hT : Gᵀ = G) (x y : ι → F) : x ⬝ᵥ G *ᵥ y = y ⬝ᵥ G *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

omit [DecidableEq ι] [CharP F 2] in
theorem vecMul_G (hT : Gᵀ = G) (x : ι → F) : Matrix.vecMul x G = G *ᵥ x := by
  rw [← Matrix.mulVec_transpose, hT]

omit [DecidableEq ι] [CharP F 2] in
private theorem shortN_mul_shortM_apply (i j : Fin 2 ⊕ Fin 2) :
    (shortN G a₁ a₂ b₁ b₂ * shortM a₁ a₂ b₁ b₂) i j =
      shortCol a₁ a₂ b₁ b₂ j ⬝ᵥ G *ᵥ shortRow a₁ a₂ b₁ b₂ i := by
  rw [Matrix.mul_apply', dotProduct_comm]
  rfl

@[expose] def ShortPairsG (G : Matrix ι ι F) (a₁ a₂ b₁ b₂ : ι → F) : Prop :=
  a₁ ⬝ᵥ G *ᵥ b₁ = 1 ∧ a₂ ⬝ᵥ G *ᵥ b₂ = 1 ∧
    (a₁ ⬝ᵥ G *ᵥ a₂ = 0 ∧ b₁ ⬝ᵥ G *ᵥ b₂ = 0 ∧ a₁ ⬝ᵥ G *ᵥ b₂ = 0 ∧ a₂ ⬝ᵥ G *ᵥ b₁ = 0)

omit [DecidableEq ι] [CharP F 2] in
theorem shortN_mul_shortM (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) : shortN G a₁ a₂ b₁ b₂ * shortM a₁ a₂ b₁ b₂ = 1 := by
  obtain ⟨h₁, h₂, h0a, h0b, h0ab, h0ba⟩ := h
  have s₁ := (formG_comm hT a₁ b₁).symm.trans h₁
  have s₂ := (formG_comm hT a₂ b₂).symm.trans h₂
  have s0a := (formG_comm hT a₁ a₂).symm.trans h0a
  have s0b := (formG_comm hT b₁ b₂).symm.trans h0b
  have s0ab := (formG_comm hT a₁ b₂).symm.trans h0ab
  have s0ba := (formG_comm hT a₂ b₁).symm.trans h0ba
  ext i j
  rw [shortN_mul_shortM_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [shortCol, shortRow, halt, h₁, h₂, h0a, h0b, h0ab, h0ba, s₁, s₂, s0a, s0b, s0ab, s0ba]

omit [DecidableEq ι] [CharP F 2] in
theorem shortM_transpose_mul_G (hT : Gᵀ = G) :
    (shortM a₁ a₂ b₁ b₂)ᵀ * G = shortG (F := F) * shortN G a₁ a₂ b₁ b₂ := by
  ext i x
  have hl : ((shortM a₁ a₂ b₁ b₂)ᵀ * G) i x = Matrix.vecMul (shortCol a₁ a₂ b₁ b₂ i) G x := rfl
  rw [hl, vecMul_G hT, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  rcases i with i | i <;> fin_cases i <;>
    simp [shortG, shortN, shortCol, shortRow, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end ShortChart

section ShortHom

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2] {G : Matrix ι ι F}
  {a₁ a₂ b₁ b₂ : ι → F}

@[expose] noncomputable def shortChartGL (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) : Matrix.SpecialLinearGroup (Fin 2) F →* GL ι F where
  toFun A :=
    ⟨gramChart (shortM a₁ a₂ b₁ b₂) (shortN G a₁ a₂ b₁ b₂) (blk2 (A : Matrix (Fin 2) (Fin 2) F)),
      gramChart (shortM a₁ a₂ b₁ b₂) (shortN G a₁ a₂ b₁ b₂)
        (blk2 ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)), by
      rw [← gramChart_mul (shortN_mul_shortM hT halt h), ← blk2_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        blk2_one, gramChart_one], by
      rw [← gramChart_mul (shortN_mul_shortM hT halt h), ← blk2_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        blk2_one, gramChart_one]⟩
  map_one' := Units.ext (by
    change gramChart _ _ (blk2 ((1 : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blk2_one, gramChart_one])
  map_mul' A B := Units.ext (by
    change gramChart _ _ (blk2 ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) = gramChart _ _ (blk2 (A : Matrix (Fin 2) (Fin 2) F)) *
        gramChart _ _ (blk2 (B : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.coe_mul, blk2_mul, gramChart_mul (shortN_mul_shortM hT halt h)])

omit [CharP F 2] in
theorem coe_shortChartGL (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((shortChartGL hT halt h A : GL ι F) : Matrix ι ι F) =
      gramChart (shortM a₁ a₂ b₁ b₂) (shortN G a₁ a₂ b₁ b₂) (blk2 (A : Matrix (Fin 2) (Fin 2) F)) :=
  rfl

theorem shortChartGL_isometry (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((shortChartGL hT halt h A : GL ι F) : Matrix ι ι F)ᵀ * G *
      ((shortChartGL hT halt h A : GL ι F) : Matrix ι ι F) = G := by
  rw [coe_shortChartGL]
  exact gramChart_isometry (shortN_mul_shortM hT halt h) hT (shortM_transpose_mul_G hT)
    shortG_transpose (blk2_isometry A)

omit [CharP F 2] in
theorem shortChartGL_injective (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) : Function.Injective (shortChartGL hT halt h) := by
  intro A B hAB
  have hNM := shortN_mul_shortM hT halt h
  have hm := congrArg (fun g : GL ι F => (g : Matrix ι ι F)) hAB
  simp only [coe_shortChartGL, gramChart] at hm
  have h1 := add_left_cancel hm
  have h2 := congrArg (fun P => shortN G a₁ a₂ b₁ b₂ * P * shortM a₁ a₂ b₁ b₂) h1
  simp only [← Matrix.mul_assoc, hNM, Matrix.one_mul] at h2
  simp only [Matrix.mul_assoc, hNM, Matrix.mul_one] at h2
  have h3 := sub_left_injective h2
  have h4 := congrArg Matrix.toBlocks₁₁ h3
  simp only [blk2, Matrix.toBlocks_fromBlocks₁₁] at h4
  exact Matrix.SpecialLinearGroup.ext A B fun i j => congrFun (congrFun h4 i) j

omit [CharP F 2] in
theorem coe_shortChartGL_sl2Upper (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) (t : F) :
    ((shortChartGL hT halt h (sl2Upper t) : GL ι F) : Matrix ι ι F) =
      1 + t • (Matrix.vecMulVec a₁ (G *ᵥ a₂) + Matrix.vecMulVec a₂ (G *ᵥ a₁)) := by
  rw [coe_shortChartGL, gramChart]
  congr 1
  ext x y
  simp [blk2, shortM, shortN, shortCol, shortRow, coe_sl2Upper, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.fromBlocks]
  ring

omit [CharP F 2] in
theorem coe_shortChartGL_sl2Lower (hT : Gᵀ = G) (halt : ∀ x, x ⬝ᵥ G *ᵥ x = 0)
    (h : ShortPairsG G a₁ a₂ b₁ b₂) (t : F) :
    ((shortChartGL hT halt h (sl2Lower t) : GL ι F) : Matrix ι ι F) =
      1 + t • (Matrix.vecMulVec b₁ (G *ᵥ b₂) + Matrix.vecMulVec b₂ (G *ᵥ b₁)) := by
  rw [coe_shortChartGL, gramChart]
  congr 1
  ext x y
  simp [blk2, shortM, shortN, shortCol, shortRow, coe_sl2Lower, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.fromBlocks]
  ring

end ShortHom

section ShortSp

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F}

abbrev ShortPairs (a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F) : Prop :=
  ShortPairsG (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₁ a₂ b₁ b₂

@[expose] noncomputable def shortChart (h : ShortPairs a₁ a₂ b₁ b₂) :
    Matrix.SpecialLinearGroup (Fin 2) F →* CFSG.Open.StatedSp n F :=
  (shortChartGL J_transpose form_self h).codRestrict (CFSG.Open.StatedSp n F) fun A => by
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
    exact shortChartGL_isometry J_transpose form_self h A

theorem shortChart_injective (h : ShortPairs a₁ a₂ b₁ b₂) : Function.Injective (shortChart h) :=
  fun _ _ hAB => shortChartGL_injective J_transpose form_self h (congrArg Subtype.val hAB)

theorem shortChart_sl2Upper_map (h : ShortPairs a₁ a₂ b₁ b₂) :
    ((sl2UpperUniSub F).map (shortChart h)).map (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₁ a₂ := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hA
    exact Subgroup.subset_closure ⟨t, coe_shortChartGL_sl2Upper J_transpose form_self h t⟩
  · rw [altSiegelGroup, Subgroup.closure_le]
    rintro g ⟨t, ht⟩
    refine ⟨shortChart h (sl2Upper t), ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, rfl⟩, ?_⟩
    apply Units.ext
    rw [ht]
    exact coe_shortChartGL_sl2Upper J_transpose form_self h t

theorem shortChart_sl2Lower_mem (h : ShortPairs a₁ a₂ b₁ b₂) (t : F) :
    (CFSG.Open.StatedSp n F).subtype (shortChart h (sl2Lower t)) ∈
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ b₂ :=
  Subgroup.subset_closure ⟨t, coe_shortChartGL_sl2Lower J_transpose form_self h t⟩

end ShortSp

section LongChart

open CFSG.LieType.SeitzGeneration.RootPair (spSL2Hom planeEmb planeProj planeProj_emb planeProj_ext)

variable {n : ℕ} {F : Type} [Field F]

private theorem one_add_smul_vecMulVec_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    (u v y : ι → F) (c : F) :
    (1 + c • Matrix.vecMulVec u v) *ᵥ y = y + (c * (v ⬝ᵥ y)) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

theorem coe_spTransvection (u : Fin n ⊕ Fin n → F) (c : F) :
    (((CFSG.RankThree.PartOne.KCSpFull.spTransvection u c : CFSG.Open.StatedSp n F) :
        GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • Matrix.vecMulVec u ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ u) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_add_smul_vecMulVec_mulVec]
  have h := CFSG.RankThree.PartOne.KCSpFull.spEnd_spTransvection u c y
  rw [CFSG.RankThree.Classical.spEnd_apply, CFSG.RankThree.Classical.spForm_apply] at h
  rw [h, dotProduct_comm ((Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ u) y]
  rfl

variable {v w : Fin n ⊕ Fin n → F}

theorem spSL2Hom_sl2Upper (hvw : CFSG.RankThree.Classical.spForm n F v w = 1) (t : F) :
    spSL2Hom hvw (sl2Upper t) = CFSG.RankThree.PartOne.KCSpFull.spTransvection v (-t) := by
  have h : sl2Upper t = CFSG.RankThree.PartOne.CTP.u2 t :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [coe_sl2Upper, CFSG.RankThree.PartOne.CTP.u2_coe]
  rw [h, CFSG.LieType.SeitzGeneration.RootPair.spSL2Hom_u2]

theorem spSL2Hom_sl2Lower (hvw : CFSG.RankThree.Classical.spForm n F v w = 1) (t : F) :
    spSL2Hom hvw (sl2Lower t) = CFSG.RankThree.PartOne.KCSpFull.spTransvection w t := by
  have h : sl2Lower t = CFSG.RankThree.PartOne.CTP.l2 t :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [coe_sl2Lower, CFSG.RankThree.PartOne.CTP.l2_coe]
  rw [h, CFSG.LieType.SeitzGeneration.RootPair.spSL2Hom_l2]

theorem spSL2Hom_injective (hvw : CFSG.RankThree.Classical.spForm n F v w = 1) :
    Function.Injective (spSL2Hom hvw) := by
  intro g g' h
  have hv : ∀ a : Fin 2 → F,
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ a = (g' : Matrix (Fin 2) (Fin 2) F) *ᵥ a := by
    intro a
    have h1 := CFSG.LieType.SeitzGeneration.RootPair.spEnd_spSL2Hom hvw g (planeEmb v w a)
    have h2 := CFSG.LieType.SeitzGeneration.RootPair.spEnd_spSL2Hom hvw g' (planeEmb v w a)
    rw [h] at h1
    have h3 := congrArg (planeProj v w) (h1.symm.trans h2)
    rwa [planeProj_ext hvw, planeProj_ext hvw, planeProj_emb hvw] at h3
  refine Matrix.SpecialLinearGroup.ext g g' fun i j => ?_
  have h4 := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h4

theorem spSL2Hom_sl2Upper_map (hvw : CFSG.RankThree.Classical.spForm n F v w = 1) :
    ((sl2UpperUniSub F).map (spSL2Hom hvw)).map (CFSG.Open.StatedSp n F).subtype =
      matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hA
    refine Subgroup.subset_closure ⟨-t, ?_⟩
    change (((spSL2Hom hvw (sl2Upper t) : CFSG.Open.StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    rw [spSL2Hom_sl2Upper, coe_spTransvection]
  · rw [matTransvGroup, Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    refine ⟨spSL2Hom hvw (sl2Upper (-c)),
      ⟨sl2Upper (-c), mem_sl2UpperUniSub_iff.mpr ⟨-c, rfl⟩, rfl⟩, ?_⟩
    apply Units.ext
    change (((spSL2Hom hvw (sl2Upper (-c)) : CFSG.Open.StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    rw [hc, spSL2Hom_sl2Upper, neg_neg, coe_spTransvection]

theorem spSL2Hom_sl2Lower_mem (hvw : CFSG.RankThree.Classical.spForm n F v w = 1) (t : F) :
    (CFSG.Open.StatedSp n F).subtype (spSL2Hom hvw (sl2Lower t)) ∈
      matTransvGroup w ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w) :=
  Subgroup.subset_closure ⟨t, by
    change (((spSL2Hom hvw (sl2Lower t) : CFSG.Open.StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    rw [spSL2Hom_sl2Lower, coe_spTransvection]⟩

end LongChart

theorem exists_models_of_chart {K K' : Type*} [Group K] [Group K'] {D : UniversalRootDatum K}
    {D' : UniversalRootDatum K'} (ι : K' →* K) (hι : Function.Injective ι)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) {β₀ : Fin D'.rank → ℤ} (hβ₀ : β₀ ∈ D'.roots)
    (c : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* K) (hc : Function.Injective c)
    (hcU : (sl2UpperUniSub (GaloisField 2 1)).map c = (D'.rootGroup β₀).map ι)
    (hcL : ∀ t, c (sl2Lower t) ∈ ι.range) (u : K)
    (hu : (D.rootGroup β).map (MulAut.conj u).toMonoidHom =
      (sl2UpperUniSub (GaloisField 2 1)).map c) :
    ∃ (model : SelectedRoot.SelectedSL2Model D (GaloisField 2 1) β)
      (model' : SelectedRoot.SelectedSL2Model D' (GaloisField 2 1) β₀),
      ∀ A, MulAut.conj u (model.phi A) = ι (model'.phi A) := by
  have hrange : ∀ A, c A ∈ ι.range := by
    intro A
    have hle : Subgroup.closure (Set.range (sl2Upper : GaloisField 2 1 → _) ∪
        Set.range (sl2Lower : GaloisField 2 1 → _)) ≤ ι.range.comap c := by
      rw [Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · have ht : c (sl2Upper t) ∈ (D'.rootGroup β₀).map ι := by
          rw [← hcU]
          exact Subgroup.mem_map_of_mem c (mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩)
        obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp ht
        exact ⟨y, hy⟩
      · exact hcL t
    exact hle (by rw [RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]; trivial)
  let e := MonoidHom.ofInjective hι
  let phi' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* K' :=
    e.symm.toMonoidHom.comp (c.codRestrict ι.range hrange)
  have hphi' : ∀ A, ι (phi' A) = c A := by
    intro A
    exact congrArg Subtype.val (e.apply_symm_apply ⟨c A, hrange A⟩)
  have hinj' : Function.Injective phi' := fun A B h => hc (by rw [← hphi', ← hphi', h])
  have hcomp : ι.comp phi' = c := MonoidHom.ext hphi'
  have hup' : (sl2UpperUniSub (GaloisField 2 1)).map phi' = D'.rootGroup β₀ := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_map, hcomp, hcU]
  let phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* K :=
    (MulAut.conj u⁻¹).toMonoidHom.comp c
  have hinj : Function.Injective phi := (MulAut.conj u⁻¹).injective.comp hc
  have hup : (sl2UpperUniSub (GaloisField 2 1)).map phi = D.rootGroup β := by
    rw [← Subgroup.map_map, ← hu, Subgroup.map_map]
    have hid : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id K := by
      ext g
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  refine ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper D β hβ phi hinj hup,
    SelectedRoot.SelectedSL2Model.ofGF2Upper D' β₀ hβ₀ phi' hinj' hup', fun A => ?_⟩
  rw [SelectedRoot.SelectedSL2Model.ofGF2Upper_phi, SelectedRoot.SelectedSL2Model.ofGF2Upper_phi,
    hphi']
  simp only [phi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

end CFSG.StandardType.FieldTwoPSp
