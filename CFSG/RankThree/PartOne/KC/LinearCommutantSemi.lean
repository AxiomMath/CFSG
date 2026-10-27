module

public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut SemiGL)

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def semilinPsi (n : ℕ) (K : Type) [Field K] :
    SemiGL (Fin n) K →* MulAut (projectiveSL n K) :=
  SemidirectProduct.lift (conjAut n K) (fieldAut n K) fun σ => MonoidHom.ext fun A => by
    have h := (standard_automorphism_transport (K := K) (n := n)).2.2.1 σ A
    rw [CFSG.RankThree.LinearDescent.map_eq_glAut] at h
    exact h.symm

theorem semilinPsi_mk (A : GL (Fin n) K) (σ : K ≃+* K) :
    semilinPsi n K ⟨A, σ⟩ = conjAut n K A * fieldAut n K σ := by
  have : (⟨A, σ⟩ : SemiGL (Fin n) K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, semilinPsi, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]

theorem semilinPsi_conj (g : SemiGL (Fin n) K) (Y : GL (Fin n) K) :
    semilinPsi n K g * conjAut n K Y * (semilinPsi n K g)⁻¹ =
      conjAut n K (g.left * glAut g.right Y * g.left⁻¹) := by
  obtain ⟨A, σ⟩ := g
  rw [semilinPsi_mk]
  have h := (standard_automorphism_transport (K := K) (n := n)).2.2.1 σ Y
  rw [CFSG.RankThree.LinearDescent.map_eq_glAut] at h
  change conjAut n K A * fieldAut n K σ * conjAut n K Y * (conjAut n K A * fieldAut n K σ)⁻¹ =
    conjAut n K (A * glAut σ Y * A⁻¹)
  rw [map_mul, map_mul, map_inv, ← h]
  group


@[expose] noncomputable def conjRingAut (n : ℕ) (K : Type) [Field K] :
    GL (Fin n) K →* RingAut (Matrix (Fin n) (Fin n) K) :=
  (MulSemiringAction.toRingAut (ConjAct (GL (Fin n) K)) (Matrix (Fin n) (Fin n) K)).comp
    (ConjAct.toConjAct : GL (Fin n) K ≃* ConjAct (GL (Fin n) K)).toMonoidHom

theorem conjRingAut_apply (A : GL (Fin n) K) (Y : Matrix (Fin n) (Fin n) K) :
    conjRingAut n K A Y =
      (A : Matrix (Fin n) (Fin n) K) * Y * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  simp [conjRingAut, ConjAct.units_smul_def]

@[expose] noncomputable def fieldRingAut (n : ℕ) (K : Type) [Field K] :
    (K ≃+* K) →* RingAut (Matrix (Fin n) (Fin n) K) where
  toFun σ := σ.mapMatrix
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

theorem fieldRingAut_apply (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    fieldRingAut n K σ Y = Y.map σ := rfl

@[expose] noncomputable def semilinAct (n : ℕ) (K : Type) [Field K] :
    SemiGL (Fin n) K →* RingAut (Matrix (Fin n) (Fin n) K) :=
  SemidirectProduct.lift (conjRingAut n K) (fieldRingAut n K) fun σ => MonoidHom.ext fun A => by
    refine RingEquiv.ext fun Y => ?_
    change conjRingAut n K (glAut σ A) Y =
      (fieldRingAut n K σ) ((conjRingAut n K A) ((fieldRingAut n K σ).symm Y))
    rw [conjRingAut_apply, conjRingAut_apply, fieldRingAut_apply]
    have h1 : (fieldRingAut n K σ).symm Y = Y.map ⇑σ.symm := rfl
    have h2 : (Y.map ⇑σ.symm).map ⇑σ = Y := by
      ext i j
      simp
    have hmul : ∀ P Q : Matrix (Fin n) (Fin n) K, (P * Q).map ⇑σ = P.map ⇑σ * Q.map ⇑σ :=
      fun P Q => Matrix.map_mul (f := (σ : K →+* K))
    rw [h1, ← map_inv (glAut σ) A, coe_glAut, coe_glAut, hmul, hmul, h2]

theorem semilinAct_mk (A : GL (Fin n) K) (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    semilinAct n K ⟨A, σ⟩ Y =
      (A : Matrix (Fin n) (Fin n) K) * Y.map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : (⟨A, σ⟩ : SemiGL (Fin n) K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, semilinAct, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  change conjRingAut n K A (fieldRingAut n K σ Y) = _
  rw [conjRingAut_apply, fieldRingAut_apply]

@[expose] noncomputable def semilinGLAct (n : ℕ) (K : Type) [Field K] :
    SemiGL (Fin n) K →* MulAut (GL (Fin n) K) :=
  SemidirectProduct.lift (MulAut.conj : GL (Fin n) K →* MulAut (GL (Fin n) K)) glAut fun σ =>
    MonoidHom.ext fun A => MulEquiv.ext fun X => by
      change glAut σ A * X * (glAut σ A)⁻¹ = glAut σ (A * (glAut σ).symm X * A⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem semilinGLAct_mk (A : GL (Fin n) K) (σ : K ≃+* K) (X : GL (Fin n) K) :
    semilinGLAct n K ⟨A, σ⟩ X = A * glAut σ X * A⁻¹ := by
  have : (⟨A, σ⟩ : SemiGL (Fin n) K) = SemidirectProduct.inl A * SemidirectProduct.inr σ :=
    SemidirectProduct.mk_eq_inl_mul_inr σ A
  rw [this, map_mul, semilinGLAct, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  rfl

theorem semilinPsi_conj_act (g : SemiGL (Fin n) K) (X : GL (Fin n) K) :
    semilinPsi n K g * conjAut n K X * (semilinPsi n K g)⁻¹ =
      conjAut n K (semilinGLAct n K g X) := by
  obtain ⟨A, σ⟩ := g
  rw [semilinGLAct_mk]
  exact semilinPsi_conj ⟨A, σ⟩ X

theorem coe_semilinGLAct (g : SemiGL (Fin n) K) (X : GL (Fin n) K) :
    ((semilinGLAct n K g X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      semilinAct n K g (X : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨A, σ⟩ := g
  rw [semilinGLAct_mk, semilinAct_mk]
  simp only [Units.val_mul, coe_glAut]


theorem commute_scalar_gl (c : Kˣ) (g : GL (Fin n) K) :
    Commute (GeneralLinearGroup.scalar (Fin n) c) g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

theorem scalar_eq_one_iff (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c = 1 ↔ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h1
    exact Units.ext h1
  · rintro rfl
    exact map_one _

theorem range_semilinPsi : (semilinPsi n K).range = semilinearAutGroup n K := by
  ext α
  rw [MonoidHom.mem_range, mem_semilinearAutGroup_iff]
  constructor
  · rintro ⟨⟨A, σ⟩, rfl⟩
    exact ⟨A, σ, semilinPsi_mk A σ⟩
  · rintro ⟨A, σ, rfl⟩
    exact ⟨⟨A, σ⟩, semilinPsi_mk A σ⟩

theorem det_semilin_conj (M : GL (Fin n) K) (σ : K ≃+* K) (a : GL (Fin n) K) :
    ((M * glAut σ a * M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      σ ((a : Matrix (Fin n) (Fin n) K).det) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, coe_glAut]
  have h1 : (M : Matrix (Fin n) (Fin n) K).det *
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h2 : ((a : Matrix (Fin n) (Fin n) K).map σ).det =
      σ ((a : Matrix (Fin n) (Fin n) K).det) := by
    rw [show (a : Matrix (Fin n) (Fin n) K).map σ =
      (σ : K →+* K).mapMatrix (a : Matrix (Fin n) (Fin n) K) from rfl, ← RingHom.map_det]
    rfl
  rw [h2]
  calc (M : Matrix (Fin n) (Fin n) K).det * σ ((a : Matrix (Fin n) (Fin n) K).det) *
        ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det
      = σ ((a : Matrix (Fin n) (Fin n) K).det) *
        ((M : Matrix (Fin n) (Fin n) K).det *
          ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) := by ring
    _ = σ ((a : Matrix (Fin n) (Fin n) K).det) := by rw [h1, mul_one]

theorem det_scalar_gl (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

section Kernel

variable [Finite K]

theorem conjAut_eq_one_iff (hn : 3 ≤ n) (A : GL (Fin n) K) :
    conjAut n K A = 1 ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = A := by
  constructor
  · intro h
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h])).2
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

theorem semilinAct_eq_one_of_psi_eq_one (hn : 3 ≤ n) (g : SemiGL (Fin n) K)
    (hg : semilinPsi n K g = 1) : semilinAct n K g = 1 := by
  obtain ⟨A, σ⟩ := g
  rw [semilinPsi_mk] at hg
  obtain ⟨hσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn A σ hg
  subst hσ
  refine RingEquiv.ext fun Y => ?_
  rw [semilinAct_mk]
  change _ * Y.map (RingEquiv.refl K) * _ = Y
  rw [show Y.map (RingEquiv.refl K) = Y from by ext; rfl]
  have hA : A = GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hAc : Commute (A : Matrix (Fin n) (Fin n) K) Y := by
    rw [hA, GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  rw [hAc.eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


variable (n K) in
@[expose] noncomputable def actE (hn : 3 ≤ n) :
    ↥(semilinPsi n K).range →* RingAut (Matrix (Fin n) (Fin n) K) :=
  MonoidHom.liftOfRightInverse (semilinPsi n K).rangeRestrict
    (Function.surjInv (semilinPsi n K).rangeRestrict_surjective)
    (Function.rightInverse_surjInv (semilinPsi n K).rangeRestrict_surjective)
    ⟨semilinAct n K, fun g hg => by
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hg
      exact (MonoidHom.mem_ker).mpr (semilinAct_eq_one_of_psi_eq_one hn g hg)⟩

theorem actE_semilinPsi (hn : 3 ≤ n) (g : SemiGL (Fin n) K) :
    actE n K hn ⟨semilinPsi n K g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ = semilinAct n K g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem semilin_conj_eq_self {p : ℕ} (hn : 3 ≤ n)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) {a : GL (Fin n) K} (hap : a ^ p = 1)
    (hdet : (a : Matrix (Fin n) (Fin n) K).det = 1) (g : SemiGL (Fin n) K)
    (hg : semilinPsi n K g * conjAut n K a * (semilinPsi n K g)⁻¹ = conjAut n K a) :
    g.left * glAut g.right a * g.left⁻¹ = a := by
  rw [semilinPsi_conj] at hg
  set b := g.left * glAut g.right a * g.left⁻¹ with hb
  have h1 : conjAut n K (b * a⁻¹) = 1 := by rw [map_mul, hg, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h1
  have hbc : b = GeneralLinearGroup.scalar (Fin n) c * a := by
    calc b = (b * a⁻¹) * a := by group
      _ = GeneralLinearGroup.scalar (Fin n) c * a := by rw [← hc]
  have hcn : c ^ n = 1 := by
    have h := det_semilin_conj g.left g.right a
    rw [← hb, hdet, map_one, hbc, Units.val_mul, Matrix.det_mul, det_scalar_gl, hdet,
      mul_one] at h
    exact Units.ext (by simpa using h)
  have hcp : c ^ p = 1 := by
    have h2 : b ^ p = 1 := by
      rw [hb, conj_pow, ← map_pow, hap, map_one, mul_one, mul_inv_cancel]
    rw [hbc, (commute_scalar_gl c a).mul_pow, hap, mul_one, ← map_pow] at h2
    exact (scalar_eq_one_iff (by omega) _).mp h2
  rw [hbc, hZp c hcp hcn, map_one, one_mul]

end Kernel

end CFSG.RankThree.PartOne.KCLinComm
