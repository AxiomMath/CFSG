module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras Matrix

namespace AutPSp

variable {n : ℕ} {K : Type} [Field K]

section Scalars

variable [CharP K 2]

theorem spScalars_eq_bot [NeZero n] : spScalars n K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hJ := SymplecticTorusWeyl.mem_statedSp_iff.mp z.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hJ
  have h1 : (c : K) * c = 1 := by
    simpa [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
  have hc1 : (c : K) = 1 := GGRootSL.eq_one_of_mul_self_eq_one h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, show c = 1 from Units.ext hc1, map_one]
  rfl

theorem proj_injective [NeZero n] : Function.Injective (proj n K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, spScalars_eq_bot]

end Scalars

section Inner

variable [Finite K] [CharP K 2]

theorem conjAut_mem_inn (A : gsp n K) :
    conjAut n K A ∈ (MulAut.conj : StatedProj (StatedSp n K) →* MulAut _).range := by
  obtain ⟨μ, hμ⟩ := A.2
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (μ : K)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact μ.ne_zero hl
  set c : GL (Fin n ⊕ Fin n) K := Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l hl0)⁻¹
  have hc : (c : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.scalar (Fin n ⊕ Fin n) l⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hcen : c ∈ Subgroup.center (GL (Fin n ⊕ Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hA₀ : c * (A : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, Units.val_mul, hc, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul]
    change l⁻¹ • l⁻¹ • (((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      formJ n K * ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) =
        formJ n K
    rw [hμ, smul_smul, smul_smul, hl, show l⁻¹ * l⁻¹ * (l * l) = 1 by field_simp, one_smul]
  refine ⟨proj n K ⟨_, hA₀⟩, ?_⟩
  rw [← conjAut_statedSp]
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, coe_conjSp]
  change c * (A : GL (Fin n ⊕ Fin n) K) * (g : GL (Fin n ⊕ Fin n) K) *
      (c * (A : GL (Fin n ⊕ Fin n) K))⁻¹ = _
  have hcomm := Subgroup.mem_center_iff.mp hcen
    ((A : GL (Fin n ⊕ Fin n) K) * (g : GL (Fin n ⊕ Fin n) K) * (A : GL (Fin n ⊕ Fin n) K)⁻¹)
  calc c * (A : GL (Fin n ⊕ Fin n) K) * (g : GL (Fin n ⊕ Fin n) K) *
        (c * (A : GL (Fin n ⊕ Fin n) K))⁻¹ =
        c * ((A : GL (Fin n ⊕ Fin n) K) * (g : GL (Fin n ⊕ Fin n) K) *
          (A : GL (Fin n ⊕ Fin n) K)⁻¹) * c⁻¹ := by group
    _ = _ := by rw [← hcomm, mul_inv_cancel_right]

end Inner

section Compl

noncomputable abbrev compl : Subgroup (MulAut (StatedProj (StatedSp n K))) :=
  (fieldAut n K).range

theorem exists_mul_compl [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (α : MulAut (StatedProj (StatedSp n K))) :
    ∃ i ∈ (MulAut.conj : StatedProj (StatedSp n K) →* MulAut _).range,
      ∃ c ∈ (compl : Subgroup (MulAut (StatedProj (StatedSp n K)))), α = i * c := by
  obtain ⟨A, σ, rfl⟩ := (automorphism_generation (K := K) hn).2 α
  exact ⟨_, conjAut_mem_inn A, _, ⟨σ, rfl⟩, rfl⟩

theorem map_E (σ : K ≃+* K) (ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex n) :
    (E K ρ).map σ = E K ρ := by
  cases ρ <;> ext a b <;> simp only [E, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.single_apply] <;> split_ifs <;> simp

theorem fieldSp_elt (σ : K ≃+* K) (ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex n) (c : K) :
    fieldSp n K σ (elt ρ c) = elt ρ (σ c) := by
  apply mat_injective
  have h : mat n K (fieldSp n K σ (elt ρ c)) = (mat n K (elt ρ c)).map σ := rfl
  rw [h, mat_elt, mat_elt]
  ext a b
  have hE := congrFun (congrFun (map_E σ ρ) a) b
  rw [Matrix.map_apply] at hE
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, hE, Matrix.one_apply]
  split_ifs <;> simp

theorem commute_elt_of_commute_elt_one {x : StatedSp n K}
    {ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex n} (h : x * elt ρ 1 * x⁻¹ = elt ρ 1)
    (t : K) : x * elt ρ t * x⁻¹ = elt ρ t := by
  have hXY : mat n K x * mat n K x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hE : mat n K x * E K ρ * mat n K x⁻¹ = E K ρ := by
    have h1 := congrArg (mat n K) h
    rw [map_mul, map_mul, mat_elt, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hXY] at h1
    exact add_left_cancel h1
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hXY,
    Matrix.mul_smul, Matrix.smul_mul, hE]

theorem inn_inf_compl [CharP K 2] [NeZero n] :
    (MulAut.conj : StatedProj (StatedSp n K) →* MulAut _).range ⊓
      (compl : Subgroup (MulAut (StatedProj (StatedSp n K)))) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, hx⟩, σ, rfl⟩
  obtain ⟨y, rfl⟩ := proj_surjective x
  set ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex n := .positiveLong 0
  have key : ∀ t : K, elt ρ (σ t) = y * elt ρ t * y⁻¹ := by
    intro t
    apply proj_injective
    have h := congrArg (fun α : MulAut (StatedProj (StatedSp n K)) => α (proj n K (elt ρ t))) hx
    simp only [MulAut.conj_apply, fieldAut_proj, fieldSp_elt] at h
    rw [← h, map_mul, map_mul, map_inv]
  have h1 : y * elt ρ 1 * y⁻¹ = elt ρ 1 := by rw [← key, map_one]
  have hσ : σ = 1 := by
    ext t
    have h2 := key t
    rw [commute_elt_of_commute_elt_one h1] at h2
    exact elt_injective ρ h2
  rw [Subgroup.mem_bot, hσ, map_one]

end Compl

end AutPSp

end CFSG.StandardType
