module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Sub
public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.Adapters.StatedQuasisimple
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Subgroup
open CFSG.GH74.L5U5

variable {K : Type} [Field K] [Finite K]

private theorem blk4_apply (A B : Matrix (Fin 2) (Fin 2) K) (a b : Fin 4) :
    blk4 A B a b = if h : a.val < 2 ∧ b.val < 2 then A ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
      else if h : 2 ≤ a.val ∧ 2 ≤ b.val then
        B ⟨a.val - 2, by omega⟩ ⟨b.val - 2, by omega⟩
      else 0 := by
  rw [blk4_eq_reindex]
  fin_cases a <;> fin_cases b <;> rfl

private theorem blk4_comm_diagonal (A B : Matrix (Fin 2) (Fin 2) K) (u : Fin 4 → K)
    (h01 : u 0 = u 1) (h23 : u 2 = u 3) :
    blk4 A B * Matrix.diagonal u = Matrix.diagonal u * blk4 A B := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blk4_apply, h01, h23, mul_comm]

private theorem diagGL_comm_diagUnit (a b : GL (Fin 2) K) (u : Fin 4 → Kˣ)
    (h01 : u 0 = u 1) (h23 : u 2 = u 3) :
    diagGL a b * diagUnit u = diagUnit u * diagGL a b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL]
  change blk4 (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) *
      Matrix.diagonal (fun i => (u i : K)) =
      Matrix.diagonal (fun i => (u i : K)) *
        blk4 (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K)
  exact blk4_comm_diagonal _ _ _ (by rw [h01]) (by rw [h23])

private theorem diagGL_comm_d₁ (ζ : CubeRoot K) (a b : GL (Fin 2) K) :
    diagGL a b * d₁ ζ = d₁ ζ * diagGL a b := by
  have hd : d₁ ζ = diagUnit (fun i => ζ.pow (![1, 1, -1, -1] i -
      ∑ j, ![1, 1, -1, -1] j)) := rfl
  rw [hd]
  exact diagGL_comm_diagUnit a b _ rfl rfl

private theorem scalar_neg_one (n : ℕ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Kˣ) : GL (Fin n) K) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Matrix.scalar_apply]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply, h]

private theorem scalar4_eq (c : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) =
      diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
             (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  apply Units.ext
  rw [coe_diagGL, blk4_eq_reindex]
  simp only [Matrix.GeneralLinearGroup.coe_scalar]
  have h : (Matrix.scalar (Fin 2) (c : K) : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hb : Matrix.fromBlocks ((c : K) • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0
      ((c : K) • (1 : Matrix (Fin 2) (Fin 2) K)) =
      (c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp
  rw [h, hb, map_smul, map_one, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

private theorem eq_scalar_of_diagGL_mem_scalars {a b : GL (Fin 2) K}
    (h : diagGL a b ∈ StatedScalars (Fin 4) K) :
    ∃ c : Kˣ, a = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      b = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h
  have h' : diagGL a b = diagGL (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) :=
    hc.symm.trans (scalar4_eq c)
  exact ⟨c, diagGL_inj h'⟩

private noncomputable def blk2Hom (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      GL (Fin 4) K where
  toFun x := diagGL (Matrix.SpecialLinearGroup.toGL x.1) (Matrix.SpecialLinearGroup.toGL x.2)
  map_one' := by simp [diagGL_one]
  map_mul' x y := by simp [diagGL_mul]

private theorem blk2Hom_injective : Function.Injective (blk2Hom K) := by
  intro x y h
  have h' : diagGL (Matrix.SpecialLinearGroup.toGL x.1) (Matrix.SpecialLinearGroup.toGL x.2) =
      diagGL (Matrix.SpecialLinearGroup.toGL y.1) (Matrix.SpecialLinearGroup.toGL y.2) := h
  obtain ⟨ha, hb⟩ := diagGL_inj h'
  exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective ha)
    (Matrix.SpecialLinearGroup.toGL_injective hb)

private noncomputable def blk2HomSL (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      StatedSL 4 K :=
  (blk2Hom K).codRestrict (StatedSL 4 K) fun x => by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    change ((diagGL (Matrix.SpecialLinearGroup.toGL x.1)
      (Matrix.SpecialLinearGroup.toGL x.2) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = 1
    rw [det_diagGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, x.1.2, x.2.2, mul_one]

private theorem blk2HomSL_injective : Function.Injective (blk2HomSL K) := by
  intro x y h
  exact blk2Hom_injective (congrArg Subtype.val h)

private theorem neg_one_ne_one {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) :
    (-1 : K) ≠ 1 := by
  intro h
  have h2 : (2 : K) ≠ 0 :=
    two_ne_zero_of_odd_card (F := K) (by rw [hK]; exact hr.odd_of_ne_two (by omega))
  apply h2
  have h11 : (1 : K) + 1 = 0 := by
    have hc := congrArg (fun x : K => x + 1) h
    rw [neg_add_cancel] at hc
    exact hc.symm
  have htwo : (2 : K) = (1 : K) + 1 := by norm_num
  rw [htwo, h11]

private noncomputable def zSL (K : Type) [Field K] : StatedSL 4 K :=
  ⟨-1, by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, Units.val_neg, Matrix.det_neg,
      Units.val_one, Matrix.det_one]
    norm_num⟩

private theorem det_scalar_two_neg_one :
    (Matrix.scalar (Fin 2) (-1 : K)).det = 1 := by
  rw [Matrix.det_fin_two, Matrix.scalar_apply]
  simp

private noncomputable def pSL (K : Type) [Field K] [Finite K] :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.scalar (Fin 2) (-1 : K), det_scalar_two_neg_one⟩

private theorem toGL_pSL : Matrix.SpecialLinearGroup.toGL (pSL K) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Kˣ) := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar]
  rfl

private theorem zSL_eq_scalar : (zSL K : GL (Fin 4) K) =
    Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) := by
  show (-1 : GL (Fin 4) K) = _
  exact (scalar_neg_one 4).symm

private theorem zSL_mem_range {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) :
    zSL K ∈ (blk2HomSL K).range := by
  refine ⟨(pSL K, pSL K), ?_⟩
  apply Subtype.ext
  show diagGL (Matrix.SpecialLinearGroup.toGL (pSL K))
      (Matrix.SpecialLinearGroup.toGL (pSL K)) = (-1 : GL (Fin 4) K)
  rw [toGL_pSL, ← scalar4_eq (-1), scalar_neg_one 4]

private theorem zSL_mem_scalars : zSL K ∈
    (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) :=
  Subgroup.mem_subgroupOf.mpr (by
    rw [zSL_eq_scalar]
    exact MonoidHom.mem_range.mpr ⟨-1, rfl⟩)

private theorem zSL_ne_one {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) :
    zSL K ≠ 1 := by
  intro h
  have h00 : ((-1 : Kˣ) : K) = (1 : K) := by
    have := congrArg (fun g : StatedSL 4 K =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h
    rw [zSL_eq_scalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
    simpa using this
  exact neg_one_ne_one hr h5 hK h00

private theorem zSL_classification {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hK : Nat.card K = r) {y : StatedSL 4 K} (hyK : y ∈ (blk2HomSL K).range)
    (hys : y ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) :
    y = 1 ∨ y = zSL K := by
  obtain ⟨p, rfl⟩ := hyK
  have hmem : diagGL (Matrix.SpecialLinearGroup.toGL p.1)
      (Matrix.SpecialLinearGroup.toGL p.2) ∈ StatedScalars (Fin 4) K :=
    Subgroup.mem_subgroupOf.mp hys
  obtain ⟨c, ha, hb⟩ := eq_scalar_of_diagGL_mem_scalars hmem
  have hdet : c ^ 2 = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det ha
    rw [Matrix.SpecialLinearGroup.coeToGL_det, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin] at h1
    exact h1.symm
  have hc : c = 1 ∨ c = -1 := by
    have hKsq : (c : K) ^ 2 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hdet
      simpa [Units.val_pow_eq_pow_val] using this
    rcases sq_eq_one_iff.mp hKsq with h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Units.ext (by simpa using h))
  rcases hc with hc | hc
  · left
    apply Subtype.ext
    rw [show (blk2HomSL K p : GL (Fin 4) K) = diagGL
      (Matrix.SpecialLinearGroup.toGL p.1)
      (Matrix.SpecialLinearGroup.toGL p.2) from rfl, ha, hb, hc]
    simp [diagGL_one]
  · right
    apply Subtype.ext
    rw [zSL_eq_scalar, show (blk2HomSL K p : GL (Fin 4) K) = diagGL
      (Matrix.SpecialLinearGroup.toGL p.1)
      (Matrix.SpecialLinearGroup.toGL p.2) from rfl, ha, hb, hc,
      ← scalar4_eq (-1), scalar_neg_one 4]

private theorem card_inf_scalars_blk2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hK : Nat.card K = r) :
    Nat.card ↥((blk2HomSL K).range ⊓
      (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) = 2 := by
  let J := (blk2HomSL K).range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)
  have hzJ : zSL K ∈ J := ⟨zSL_mem_range hr h5 hK, zSL_mem_scalars⟩
  have hclass : ∀ y : ↥J, y = 1 ∨ y = ⟨zSL K, hzJ⟩ := by
    intro y
    obtain ⟨hyK, hys⟩ := Subgroup.mem_inf.mp y.2
    rcases zSL_classification hr h5 hK hyK hys with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  refine Nat.card_eq_two_iff.mpr ⟨1, ⟨zSL K, hzJ⟩, ?_, ?_⟩
  · intro h
    exact zSL_ne_one hr h5 hK (congrArg Subtype.val h).symm
  · rw [Set.eq_univ_iff_forall]
    intro y
    rcases hclass y with h | h <;> simp [h]

private theorem blk2HomSL_mem_centralizer {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hK : Nat.card K = r) (ζ : CubeRoot K) (d : StatedSL 4 K)
    (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    (blk2HomSL K).range ≤ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro hg hgh
  rw [Set.mem_singleton_iff] at hgh
  rw [hgh]
  apply Subtype.ext
  change (d : GL (Fin 4) K) * (blk2HomSL K x : GL (Fin 4) K) =
    (blk2HomSL K x : GL (Fin 4) K) * (d : GL (Fin 4) K)
  rw [hd]
  change d₁ ζ * diagGL (Matrix.SpecialLinearGroup.toGL x.1)
      (Matrix.SpecialLinearGroup.toGL x.2) =
    diagGL (Matrix.SpecialLinearGroup.toGL x.1)
      (Matrix.SpecialLinearGroup.toGL x.2) * d₁ ζ
  exact (diagGL_comm_d₁ ζ _ _).symm

theorem sub8_block_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) (d : StatedSL 4 K) (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    ∃ K₁ : Subgroup (StatedSL 4 K), K₁ ≤ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) ∧
      Nonempty (K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nat.card ↥(K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) = 2 := by
  refine ⟨(blk2HomSL K).range, blk2HomSL_mem_centralizer hr h5 hK ζ d hd, ?_, ?_⟩
  · exact ⟨(MonoidHom.ofInjective blk2HomSL_injective).symm⟩
  · exact card_inf_scalars_blk2 hr h5 hK

theorem sub8Fact_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) : Sub8Fact (StatedSL 4 K) ζ r := by
  intro d hd
  obtain ⟨K₁, hle, ⟨e⟩, hz⟩ := sub8_block_sl hr h5 hK ζ d hd
  obtain ⟨hperf, hns, hcard⟩ := sl2sq_perfect hr h5 hK e
  have hZc : K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) ≤
      Subgroup.center (StatedSL 4 K) :=
    inf_le_right.trans (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
  refine ⟨K₁, hle, hperf, hns, hcard, hz, fun N h1 h2 h3 h4 => ?_⟩
  exact (sl2sq_odd hr h5 hK e inf_le_left hZc hz N h1 h2 h3 h4).trans inf_le_right

private def blk3Mat (X : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 1) (Fin 1) K))

private theorem blk3Mat_mul (X Y : Matrix (Fin 3) (Fin 3) K) :
    blk3Mat (X * Y) = blk3Mat X * blk3Mat Y := by
  unfold blk3Mat
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

private theorem blk3Mat_one : blk3Mat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold blk3Mat
  rw [Matrix.fromBlocks_one]
  simp

private theorem blk3Mat_det (X : Matrix (Fin 3) (Fin 3) K) : (blk3Mat X).det = X.det := by
  unfold blk3Mat
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

private theorem blk3Mat_apply (X : Matrix (Fin 3) (Fin 3) K) (a b : Fin 4) :
    blk3Mat X a b = if h : a.val < 3 ∧ b.val < 3 then X ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
      else if a = b then 1 else 0 := by
  unfold blk3Mat
  fin_cases a <;> fin_cases b <;> rfl

private theorem blk3Mat_inj {X Y : Matrix (Fin 3) (Fin 3) K}
    (h : blk3Mat X = blk3Mat Y) : X = Y := by
  ext a b
  have h1 := congrArg (fun Z : Matrix (Fin 4) (Fin 4) K => Z ⟨a, by omega⟩ ⟨b, by omega⟩) h
  simpa [blk3Mat_apply] using h1

private noncomputable def blk3GL (A : GL (Fin 3) K) : GL (Fin 4) K where
  val := blk3Mat (A : Matrix (Fin 3) (Fin 3) K)
  inv := blk3Mat (A⁻¹ : GL (Fin 3) K)
  val_inv := by
    rw [← blk3Mat_mul, A.mul_inv, blk3Mat_one]
  inv_val := by
    rw [← blk3Mat_mul, A.inv_mul, blk3Mat_one]

private noncomputable def blk3GLHom (K : Type) [Field K] [Finite K] :
    GL (Fin 3) K →* GL (Fin 4) K where
  toFun := blk3GL
  map_one' := by apply Units.ext; exact blk3Mat_one
  map_mul' A B := by apply Units.ext; exact blk3Mat_mul _ _

private theorem blk3GL_injective : Function.Injective (blk3GLHom K) := by
  intro A B h
  apply Units.ext
  exact blk3Mat_inj (K := K) (by
    simpa [blk3GLHom, blk3GL] using
      congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h)

private theorem blk3Mat_comm_diagonal (X : Matrix (Fin 3) (Fin 3) K) (u : Fin 4 → K)
    (h01 : u 0 = u 1) (h12 : u 1 = u 2) :
    blk3Mat X * Matrix.diagonal u = Matrix.diagonal u * blk3Mat X := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blk3Mat_apply, h01, h12, mul_comm]

private theorem blk3GL_comm_diagUnit (A : GL (Fin 3) K) (u : Fin 4 → Kˣ)
    (h01 : u 0 = u 1) (h12 : u 1 = u 2) :
    blk3GL A * diagUnit u = diagUnit u * blk3GL A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change blk3Mat (A : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (fun i => (u i : K)) =
      Matrix.diagonal (fun i => (u i : K)) *
        blk3Mat (A : Matrix (Fin 3) (Fin 3) K)
  exact blk3Mat_comm_diagonal _ _ (by rw [h01]) (by rw [h12])

private theorem blk3GL_comm_d₃ (ζ : CubeRoot K) (A : GL (Fin 3) K) :
    blk3GL A * d₃ ζ = d₃ ζ * blk3GL A := by
  have hd : d₃ ζ = diagUnit (fun i => ζ.pow (![1, 1, 1, 0] i -
      ∑ j, ![1, 1, 1, 0] j)) := rfl
  rw [hd]
  exact blk3GL_comm_diagUnit A _ rfl rfl

private theorem blk3GL_mem_statedSL (A : GL (Fin 3) K) (hA : A ∈ StatedSL 3 K) :
    blk3GL A ∈ StatedSL 4 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  change (blk3Mat (A : Matrix (Fin 3) (Fin 3) K)).det = 1
  rw [blk3Mat_det]
  exact CFSG.Open.StatedAPI.det_of_mem_statedSL hA

private noncomputable def blk3SL (K : Type) [Field K] [Finite K] :
    StatedSL 3 K →* StatedSL 4 K :=
  ((blk3GLHom K).comp (Subgroup.subtype (StatedSL 3 K))).codRestrict (StatedSL 4 K)
    fun A => blk3GL_mem_statedSL (A : GL (Fin 3) K) A.2

private theorem blk3SL_injective : Function.Injective (blk3SL K) := by
  intro A B h
  apply Subtype.ext
  exact blk3GL_injective (congrArg Subtype.val h)

private theorem blk3SL_mem_centralizer {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hK : Nat.card K = r) (ζ : CubeRoot K) (d : StatedSL 4 K)
    (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    (blk3SL K).range ≤ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro hg hgh
  rw [Set.mem_singleton_iff] at hgh
  rw [hgh]
  apply Subtype.ext
  change (d : GL (Fin 4) K) * (blk3SL K x : GL (Fin 4) K) =
    (blk3SL K x : GL (Fin 4) K) * (d : GL (Fin 4) K)
  rw [hd]
  change d₃ ζ * blk3GL (x : GL (Fin 3) K) =
    blk3GL (x : GL (Fin 3) K) * d₃ ζ
  exact (blk3GL_comm_d₃ ζ _).symm

private theorem blk3SL_apply_three_three (x : StatedSL 3 K) :
    (((blk3SL K x : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
  show (blk3Mat ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 3 = 1
  rw [blk3Mat_apply]
  simp

private theorem blk3_inf_scalars_eq_bot {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hK : Nat.card K = r) :
    (blk3SL K).range ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyK, hys⟩
  obtain ⟨x, rfl⟩ := hyK
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.mp hys)
  rw [Subgroup.mem_bot]
  have h1 : ((c : Kˣ) : K) = 1 := by
    have h2 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 3 3) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      blk3SL_apply_three_three] at h2
    simpa using h2
  have hc1 : c = 1 := Units.ext (by simpa using h1)
  apply Subtype.ext
  change (blk3SL K x : GL (Fin 4) K) = 1
  rw [← hc, hc1]
  simp

theorem sub9_block_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) (d : StatedSL 4 K) (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    ∃ K₃ : Subgroup (StatedSL 4 K), K₃ ≤ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) ∧
      Nonempty (K₃ ≃* StatedSL 3 K) ∧
      K₃ ⊓ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
  refine ⟨(blk3SL K).range, blk3SL_mem_centralizer hr h5 hK ζ d hd, ?_,
    blk3_inf_scalars_eq_bot hr h5 hK⟩
  exact ⟨(MonoidHom.ofInjective blk3SL_injective).symm⟩

theorem sl3_block_data {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    {K₃ : Subgroup (StatedSL 4 K)} (e : K₃ ≃* StatedSL 3 K) :
    ⁅K₃, K₃⁆ = K₃ ∧ IsSimpleGroup (K₃ ⧸ Subgroup.center K₃) ∧ 2 ∣ Nat.card K₃ := by
  have hq : CFSG.IsQuasisimple ↥(StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) K
  have hq3 : CFSG.IsQuasisimple ↥K₃ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  obtain ⟨hperf, hsimple, -⟩ := (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K₃).1.mp hq3
  haveI : Group.IsPerfect ↥K₃ := hperf
  refine ⟨Subgroup.commutator_eq_self, hsimple, ?_⟩
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hK]
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  have h2 : 2 ∣ r ^ 2 - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)
  obtain ⟨t, ht⟩ := h2
  exact ⟨t * (r ^ 3 - 1) * r ^ 3, by rw [ht]; ring⟩

theorem sub9Fact_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) : Sub9Fact (StatedSL 4 K) ζ := by
  intro d hd
  obtain ⟨K₃, hle, ⟨e⟩, hz⟩ := sub9_block_sl hr h5 hK ζ d hd
  obtain ⟨hp, hs, hev⟩ := sl3_block_data hr h5 hK e
  obtain ⟨hns, hN⟩ := quasisimple_facts hp hs hev
  exact ⟨K₃, hle, hns, hz, hN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
