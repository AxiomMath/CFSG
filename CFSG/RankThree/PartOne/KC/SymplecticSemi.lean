module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv glFieldAut)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff)

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def gspAut (r : ℕ) (K : Type) [Field K] :
    (K ≃+* K) →* MulAut (gsp r K) :=
  restrictAutHom (glFieldAut (Fin r ⊕ Fin r) K) (gsp r K) fun σ _ hg => glFieldEquiv_mem_gsp σ hg

theorem coe_gspAut (σ : K ≃+* K) (A : gsp r K) :
    ((gspAut r K σ A : gsp r K) : GL (Fin r ⊕ Fin r) K) =
      glFieldEquiv (Fin r ⊕ Fin r) σ (A : GL (Fin r ⊕ Fin r) K) := rfl

theorem gspAut_apply (σ : K ≃+* K) (A : gsp r K) : gspAut r K σ A = gspFieldMap σ A := rfl

theorem coe_glFieldEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K) (A : GL ι K) :
    ((glFieldEquiv ι σ A : GL ι K) : Matrix ι ι K) = (A : Matrix ι ι K).map σ := rfl

abbrev SemiGSp (r : ℕ) (K : Type) [Field K] : Type := gsp r K ⋊[gspAut r K] (K ≃+* K)

@[expose] noncomputable def spPsi (r : ℕ) (K : Type) [Field K] :
    SemiGSp r K →* MulAut (StatedProj (StatedSp r K)) :=
  SemidirectProduct.lift (conjAut r K) (fieldAut r K) fun σ => MonoidHom.ext fun A =>
    (fieldAut_mul_conjAut_mul_inv (r := r) (K := K) σ A).symm

theorem spPsi_mk (A : gsp r K) (σ : K ≃+* K) :
    spPsi r K ⟨A, σ⟩ = conjAut r K A * fieldAut r K σ := by
  have : (⟨A, σ⟩ : SemiGSp r K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, spPsi, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]

theorem spPsi_conj (g : SemiGSp r K) (Y : gsp r K) :
    spPsi r K g * conjAut r K Y * (spPsi r K g)⁻¹ =
      conjAut r K (g.left * gspAut r K g.right Y * g.left⁻¹) := by
  obtain ⟨A, σ⟩ := g
  rw [spPsi_mk]
  have h := fieldAut_mul_conjAut_mul_inv (r := r) (K := K) σ Y
  change conjAut r K A * fieldAut r K σ * conjAut r K Y * (conjAut r K A * fieldAut r K σ)⁻¹ =
    conjAut r K (A * gspAut r K σ Y * A⁻¹)
  rw [map_mul, map_mul, map_inv, gspAut_apply, ← h]
  group

theorem range_spPsi : (spPsi r K).range = spSemilinearAutGroup r K := by
  apply le_antisymm
  · rintro _ ⟨⟨A, σ⟩, rfl⟩
    rw [spPsi_mk]
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hD | ⟨σ, rfl⟩)
    · have : spLinearAutGroup r K ≤ (spPsi r K).range := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨A, rfl⟩
        refine ⟨⟨A, 1⟩, ?_⟩
        rw [spPsi_mk, map_one, mul_one]
      exact this hD
    · refine ⟨⟨1, σ⟩, ?_⟩
      rw [spPsi_mk, map_one, one_mul]

theorem mem_spSemilinearAutGroup_iff {α : MulAut (StatedProj (StatedSp r K))} :
    α ∈ spSemilinearAutGroup r K ↔ ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ := by
  rw [← range_spPsi, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨A, σ⟩, rfl⟩
    exact ⟨A, σ, spPsi_mk A σ⟩
  · rintro ⟨A, σ, rfl⟩
    exact ⟨⟨A, σ⟩, spPsi_mk A σ⟩

section Generic

@[expose] noncomputable def glConjRingAut (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type)
    [Field K] : GL ι K →* RingAut (Matrix ι ι K) :=
  (MulSemiringAction.toRingAut (ConjAct (GL ι K)) (Matrix ι ι K)).comp
    (ConjAct.toConjAct : GL ι K ≃* ConjAct (GL ι K)).toMonoidHom

theorem glConjRingAut_apply {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (A : GL ι K) (Y : Matrix ι ι K) :
    glConjRingAut ι K A Y = (A : Matrix ι ι K) * Y * ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
  simp [glConjRingAut, ConjAct.units_smul_def]

@[expose] noncomputable def fieldMatRingAut (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type)
    [Field K] : (K ≃+* K) →* RingAut (Matrix ι ι K) where
  toFun σ := σ.mapMatrix
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

theorem fieldMatRingAut_apply {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (σ : K ≃+* K) (Y : Matrix ι ι K) : fieldMatRingAut ι K σ Y = Y.map σ := rfl

end Generic

@[expose] noncomputable def spSemilinAct (r : ℕ) (K : Type) [Field K] :
    SemiGSp r K →* RingAut (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  SemidirectProduct.lift ((glConjRingAut (Fin r ⊕ Fin r) K).comp (gsp r K).subtype)
    (fieldMatRingAut (Fin r ⊕ Fin r) K) fun σ => MonoidHom.ext fun A => by
      refine RingEquiv.ext fun Y => ?_
      change glConjRingAut (Fin r ⊕ Fin r) K
          (glFieldEquiv (Fin r ⊕ Fin r) σ (A : GL (Fin r ⊕ Fin r) K)) Y =
        (fieldMatRingAut (Fin r ⊕ Fin r) K σ) ((glConjRingAut (Fin r ⊕ Fin r) K
          (A : GL (Fin r ⊕ Fin r) K)) ((fieldMatRingAut (Fin r ⊕ Fin r) K σ).symm Y))
      rw [glConjRingAut_apply, glConjRingAut_apply, fieldMatRingAut_apply]
      have h1 : (fieldMatRingAut (Fin r ⊕ Fin r) K σ).symm Y = Y.map ⇑σ.symm := rfl
      have h2 : (Y.map ⇑σ.symm).map ⇑σ = Y := by
        ext i j
        simp
      have hmul : ∀ P Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
          (P * Q).map ⇑σ = P.map ⇑σ * Q.map ⇑σ := fun P Q => Matrix.map_mul (f := (σ : K →+* K))
      rw [h1, ← map_inv (glFieldEquiv (Fin r ⊕ Fin r) σ), coe_glFieldEquiv, coe_glFieldEquiv,
        hmul, hmul, h2]

theorem spSemilinAct_mk (A : gsp r K) (σ : K ≃+* K) (Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    spSemilinAct r K ⟨A, σ⟩ Y =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * Y.map σ *
        (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have : (⟨A, σ⟩ : SemiGSp r K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, spSemilinAct, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  change glConjRingAut (Fin r ⊕ Fin r) K (A : GL (Fin r ⊕ Fin r) K)
    (fieldMatRingAut (Fin r ⊕ Fin r) K σ Y) = _
  rw [glConjRingAut_apply, fieldMatRingAut_apply]

@[expose] noncomputable def spSemilinGAct (r : ℕ) (K : Type) [Field K] :
    SemiGSp r K →* MulAut (gsp r K) :=
  SemidirectProduct.lift (MulAut.conj : gsp r K →* MulAut (gsp r K)) (gspAut r K) fun σ =>
    MonoidHom.ext fun A => MulEquiv.ext fun X => by
      change gspAut r K σ A * X * (gspAut r K σ A)⁻¹ =
        gspAut r K σ (A * (gspAut r K σ).symm X * A⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem spSemilinGAct_mk (A : gsp r K) (σ : K ≃+* K) (X : gsp r K) :
    spSemilinGAct r K ⟨A, σ⟩ X = A * gspAut r K σ X * A⁻¹ := by
  have : (⟨A, σ⟩ : SemiGSp r K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, spSemilinGAct, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  rfl

theorem spPsi_conj_act (g : SemiGSp r K) (X : gsp r K) :
    spPsi r K g * conjAut r K X * (spPsi r K g)⁻¹ = conjAut r K (spSemilinGAct r K g X) := by
  obtain ⟨A, σ⟩ := g
  rw [spSemilinGAct_mk]
  exact spPsi_conj ⟨A, σ⟩ X

theorem coe_spSemilinGAct (g : SemiGSp r K) (X : gsp r K) :
    (((spSemilinGAct r K g X : gsp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      spSemilinAct r K g (((X : gsp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  obtain ⟨A, σ⟩ := g
  rw [spSemilinGAct_mk, spSemilinAct_mk]
  rfl

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem commute_scalar_gl (c : Kˣ) (g : GL ι K) :
    Commute (GeneralLinearGroup.scalar ι c) g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

theorem scalar_eq_one_iff [Nonempty ι] (c : Kˣ) :
    GeneralLinearGroup.scalar ι c = 1 ↔ c = 1 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h1
    exact Units.ext h1
  · rintro rfl
    exact map_one _

theorem eq_one_of_sq_eq_one_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : Odd p) {c : G}
    (h2 : c ^ 2 = 1) (hc : c ^ p = 1) : c = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have : c ^ (2 * k + 1) = c := by
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact hc

end Scalars

section Kernel

variable [Finite K]

theorem conjAut_eq_one_iff (hr : 1 ≤ r) (A : gsp r K) :
    conjAut r K A = 1 ↔ ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  have h := conjAut_mul_fieldAut_eq_one_iff hr A 1
  rw [map_one, mul_one] at h
  rw [h]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem spPsi_eq_one_iff (hr : 1 ≤ r) (g : SemiGSp r K) :
    spPsi r K g = 1 ↔ g.right = 1 ∧ ∃ c : Kˣ, (g.left : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  obtain ⟨A, σ⟩ := g
  rw [spPsi_mk]
  exact (conjAut_mul_fieldAut_eq_one_iff hr A σ).trans Iff.rfl

omit [Finite K] in
theorem scalar_mem_statedSp_iff (hr : 1 ≤ r) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K ↔ c ^ 2 = 1 :=
  CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr c

theorem sp_semilin_conj_eq_self {p : ℕ} (hr : 1 ≤ r) (hp : Odd p) {X : gsp r K}
    (hX : (X : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K) (hXp : X ^ p = 1) (g : SemiGSp r K)
    (hg : spPsi r K g * conjAut r K X * (spPsi r K g)⁻¹ = conjAut r K X) :
    g.left * gspAut r K g.right X * g.left⁻¹ = X := by
  rw [spPsi_conj] at hg
  set b := g.left * gspAut r K g.right X * g.left⁻¹ with hb
  have h1 : conjAut r K (b * X⁻¹) = 1 := by rw [map_mul, hg, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hr _).mp h1
  have hbX : (b : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * (X : GL (Fin r ⊕ Fin r) K) := by
    have : ((b * X⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K) =
        (b : GL (Fin r ⊕ Fin r) K) * (X : GL (Fin r ⊕ Fin r) K)⁻¹ := rfl
    rw [this] at hc
    calc (b : GL (Fin r ⊕ Fin r) K) =
        ((b : GL (Fin r ⊕ Fin r) K) * (X : GL (Fin r ⊕ Fin r) K)⁻¹) * (X : GL (Fin r ⊕ Fin r) K) :=
          by group
      _ = _ := by rw [hc]
  have hbSp : (b : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    have : (b : GL (Fin r ⊕ Fin r) K) = (g.left : GL (Fin r ⊕ Fin r) K) *
        glFieldEquiv (Fin r ⊕ Fin r) g.right (X : GL (Fin r ⊕ Fin r) K) *
          (g.left : GL (Fin r ⊕ Fin r) K)⁻¹ := rfl
    rw [this]
    exact conj_mem_statedSp g.left.2 (fieldEquiv_mem_statedSp g.right hX)
  have hcSp : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K := by
    have : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c =
        (b : GL (Fin r ⊕ Fin r) K) * (X : GL (Fin r ⊕ Fin r) K)⁻¹ := by
      rw [hbX]
      group
    rw [this]
    exact mul_mem hbSp (inv_mem hX)
  have hc2 : c ^ 2 = 1 := (scalar_mem_statedSp_iff hr c).mp hcSp
  have hbp : b ^ p = 1 := by
    rw [hb, conj_pow, ← map_pow, hXp, map_one, mul_one, mul_inv_cancel]
  have hcp : c ^ p = 1 := by
    have h2 : (b : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hbp, Subgroup.coe_one]
    have hX' : (X : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hXp, Subgroup.coe_one]
    rw [hbX, (commute_scalar_gl c (X : GL (Fin r ⊕ Fin r) K)).mul_pow, hX', mul_one, ← map_pow]
      at h2
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
    exact (scalar_eq_one_iff (ι := Fin r ⊕ Fin r) _).mp h2
  have hc1 : c = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hp hc2 hcp
  apply Subtype.ext
  rw [hbX, hc1, map_one, one_mul]

end Kernel

section ActE

variable [Finite K]

theorem spSemilinAct_eq_one_of_psi_eq_one (hr : 1 ≤ r) (g : SemiGSp r K)
    (hg : spPsi r K g = 1) : spSemilinAct r K g = 1 := by
  obtain ⟨A, σ⟩ := g
  obtain ⟨hσ, c, hc⟩ := (spPsi_eq_one_iff hr ⟨A, σ⟩).mp hg
  change σ = 1 at hσ
  change (A : GL (Fin r ⊕ Fin r) K) = _ at hc
  subst hσ
  refine RingEquiv.ext fun Y => ?_
  rw [spSemilinAct_mk]
  change _ * Y.map (RingEquiv.refl K) * _ = Y
  rw [show Y.map (RingEquiv.refl K) = Y from by ext; rfl]
  have hAc : Commute ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) Y := by
    rw [hc, GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  rw [hAc.eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

variable (r K) in
@[expose] noncomputable def spActE (hr : 1 ≤ r) :
    ↥(spPsi r K).range →* RingAut (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  MonoidHom.liftOfRightInverse (spPsi r K).rangeRestrict
    (Function.surjInv (spPsi r K).rangeRestrict_surjective)
    (Function.rightInverse_surjInv (spPsi r K).rangeRestrict_surjective)
    ⟨spSemilinAct r K, fun g hg => by
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hg
      exact (MonoidHom.mem_ker).mpr (spSemilinAct_eq_one_of_psi_eq_one hr g hg)⟩

theorem spActE_spPsi (hr : 1 ≤ r) (g : SemiGSp r K) :
    spActE r K hr ⟨spPsi r K g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ = spSemilinAct r K g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem spActE_eq_of_commute {p : ℕ} (hr : 1 ≤ r) (hp : Odd p) {X : gsp r K}
    (hX : (X : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K) (hXp : X ^ p = 1)
    (α : ↥(spPsi r K).range)
    (hα : (α : MulAut (StatedProj (StatedSp r K))) * conjAut r K X =
      conjAut r K X * (α : MulAut (StatedProj (StatedSp r K)))) :
    spActE r K hr α ((X : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((X : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  obtain ⟨⟨M, σ⟩, hg⟩ := α.2
  have hαeq : α = ⟨spPsi r K ⟨M, σ⟩, ⟨⟨M, σ⟩, rfl⟩⟩ := Subtype.ext hg.symm
  have hcomm : spPsi r K ⟨M, σ⟩ * conjAut r K X * (spPsi r K ⟨M, σ⟩)⁻¹ = conjAut r K X := by
    rw [hg, hα, mul_inv_cancel_right]
  have h1 := sp_semilin_conj_eq_self hr hp hX hXp ⟨M, σ⟩ hcomm
  rw [hαeq, spActE_spPsi hr ⟨M, σ⟩, ← coe_spSemilinGAct, spSemilinGAct_mk]
  exact congrArg (fun g : gsp r K => ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1

end ActE

end CFSG.RankThree.PartOne.KCSpComm
