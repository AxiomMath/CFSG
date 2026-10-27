module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofUniEmb
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open Matrix
open scoped MatrixGroups

section UniExt

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem glAut_eq_map (σ : K ≃+* K) (X : GL (Fin 3) K) :
    UnitaryHigher.glAut σ X = GeneralLinearGroup.map (σ : K →+* K) X :=
  Units.ext rfl

variable {h}

theorem conjAut_fieldAut_eq_of_psu [Finite K] {A B : unitaryIsom3 h} {σ τ : K ≃+* K}
    (heq : psuConj h A * psuField h σ = psuConj h B * psuField h τ) :
    conjAut 3 K A * fieldAut 3 K σ = conjAut 3 K B * fieldAut 3 K τ := by
  have h1 : psuConj h ⟨UnitaryHigher.glAut τ⁻¹ ((B⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K),
      glAut_mem_unitaryIsom3 τ⁻¹ (B⁻¹ * A).2⟩ * psuField h (τ⁻¹ * σ) = 1 := by
    rw [← psuField_mul_psuConj_mul_inv, map_mul, map_mul, map_inv, map_inv]
    calc (psuField h τ)⁻¹ * ((psuConj h B)⁻¹ * psuConj h A) * (psuField h τ)⁻¹⁻¹ *
          ((psuField h τ)⁻¹ * psuField h σ) =
        (psuConj h B * psuField h τ)⁻¹ * (psuConj h A * psuField h σ) := by group
      _ = 1 := by rw [heq, inv_mul_cancel]
  obtain ⟨hστ, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
  have hστ' : σ = τ := (inv_mul_eq_one.mp hστ).symm
  have hBA : ((B⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) =
      UnitaryHigher.glAut τ (GeneralLinearGroup.scalar (Fin 3) c) := by
    rw [← hc, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hc1 : conjAut 3 K ((B⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) = 1 := by
    rw [hBA, glAut_eq_map, ← (standard_automorphism_transport (n := 3) (K := K)).2.2.1 τ,
      conjAut_scalar, mul_one, mul_inv_cancel]
  have hAB : conjAut 3 K A = conjAut 3 K B := by
    have e : ((B⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) = (B : GL (Fin 3) K)⁻¹ * A := rfl
    rw [e, map_mul, map_inv, inv_mul_eq_one] at hc1
    exact hc1.symm
  rw [hAB, hστ']

variable (h)

@[expose] noncomputable def extFun (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    MulAut (projectiveSL 3 K) :=
  conjAut 3 K ((exists_psuConj_mul_psuField hq α).choose : GL (Fin 3) K) *
    fieldAut 3 K (exists_psuConj_mul_psuField hq α).choose_spec.choose

variable {h}

theorem extFun_eq [Finite K] (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)} {A : unitaryIsom3 h}
    {σ : K ≃+* K} (hα : α = psuConj h A * psuField h σ) :
    extFun h hq α = conjAut 3 K A * fieldAut 3 K σ :=
  conjAut_fieldAut_eq_of_psu
    ((exists_psuConj_mul_psuField hq α).choose_spec.choose_spec.symm.trans hα)

variable (h)

@[expose] noncomputable def extAut [Finite K] (hq : 2 < p ^ f) :
    MulAut (unitaryPSU h 3) →* MulAut (projectiveSL 3 K) where
  toFun := extFun h hq
  map_one' := by
    rw [extFun_eq hq (A := 1) (σ := 1) (by rw [map_one, map_one, mul_one]), Subgroup.coe_one,
      map_one, map_one, mul_one]
  map_mul' α β := by
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    obtain ⟨B, τ, rfl⟩ := exists_psuConj_mul_psuField hq β
    have hαβ : psuConj h A * psuField h σ * (psuConj h B * psuField h τ) =
        psuConj h (A * ⟨UnitaryHigher.glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩) *
          psuField h (σ * τ) := by
      rw [map_mul, map_mul, ← psuField_mul_psuConj_mul_inv]
      group
    rw [extFun_eq hq hαβ, extFun_eq hq rfl, extFun_eq hq rfl]
    have e : ((A * ⟨UnitaryHigher.glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ : unitaryIsom3 h) :
        GL (Fin 3) K) = (A : GL (Fin 3) K) * GeneralLinearGroup.map (σ : K →+* K) B := by
      rw [Subgroup.coe_mul]
      change (A : GL (Fin 3) K) * UnitaryHigher.glAut σ (B : GL (Fin 3) K) = _
      rw [glAut_eq_map]
    rw [e, map_mul, map_mul]
    calc conjAut 3 K A * conjAut 3 K (GeneralLinearGroup.map (σ : K →+* K) B) *
          (fieldAut 3 K σ * fieldAut 3 K τ) =
        conjAut 3 K A * (conjAut 3 K (GeneralLinearGroup.map (σ : K →+* K) B) *
          fieldAut 3 K σ) * fieldAut 3 K τ := by group
      _ = _ := by rw [← fieldAut_mul_conjAut]; group

variable {h}

theorem extAut_eq [Finite K] (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)} {A : unitaryIsom3 h}
    {σ : K ≃+* K} (hα : α = psuConj h A * psuField h σ) :
    extAut h hq α = conjAut 3 K A * fieldAut 3 K σ :=
  extFun_eq hq hα

theorem extAut_apply [Finite K] (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3))
    (x : unitaryPSU h 3) : extAut h hq α (psuToPSL h x) = psuToPSL h (α x) := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  rw [extAut_eq hq rfl, conjAut_fieldAut_psuToPSL]

theorem extAut_injective [Finite K] (hq : 2 < p ^ f) : Function.Injective (extAut h hq) := by
  intro α β hαβ
  ext x
  apply psuToPSL_injective h
  rw [← extAut_apply hq, ← extAut_apply hq, hαβ]

theorem extAut_mem_semilinear [Finite K] (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    extAut h hq α ∈ semilinearAutGroup 3 K := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  rw [extAut_eq hq rfl]
  exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    (fieldAut_mem_semilinearAutGroup _)

theorem extAut_conj [Finite K] (hq : 2 < p ^ f) (y : unitaryPSU h 3) :
    extAut h hq (MulAut.conj y) = MulAut.conj (psuToPSL h y) := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [conj_mk_eq_psuConj, extAut_eq hq (A := ⟨g, unitarySU_le_unitaryIsom3 g.2⟩) (σ := 1)
      (by rw [map_one, mul_one]), map_one, mul_one, psuToPSL_mk, ← conjAut_toGL, toGL_suToSL]

variable (h)

@[expose] noncomputable def barE : K ≃+* K where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

@[expose] noncomputable def gammaAut : MulAut (projectiveSL 3 K) :=
  fieldAut 3 K (barE h) * dualAut 3 K

variable {h}

theorem barE_mul_self : barE h * barE h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

theorem gammaAut_proj (g : SL(3, K)) :
    gammaAut h (proj 3 K g) =
      proj 3 K (Matrix.SpecialLinearGroup.map (barE h : K →+* K) (g⁻¹).transpose) := by
  rw [gammaAut, MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  rfl

theorem map_bar_inverseTranspose (A : unitaryIsom3 h) :
    GeneralLinearGroup.map (barE h : K →+* K)
      (GeneralLinearGroup.inverseTranspose (A : GL (Fin 3) K)) = A := by
  have hA := mem_unitaryIsom3.mp A.2
  have hinv : (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ :=
    Units.inv_eq_of_mul_eq_one_left hA
  apply Units.ext
  change ((((GeneralLinearGroup.inverseTranspose (A : GL (Fin 3) K) : GL (Fin 3) K)) :
    Matrix (Fin 3) (Fin 3) K)).map h.bar = _
  rw [GeneralLinearGroup.coe_inverseTranspose, hinv, transpose_transpose]
  ext i j
  simp [h.bar_bar]

theorem gammaAut_comm [Finite K] (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    gammaAut h * extAut h hq α = extAut h hq α * gammaAut h := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  rw [extAut_eq hq rfl, gammaAut]
  have hc : fieldAut 3 K (barE h) * dualAut 3 K * conjAut 3 K A =
      conjAut 3 K A * (fieldAut 3 K (barE h) * dualAut 3 K) := by
    rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, fieldAut_mul_conjAut,
      map_bar_inverseTranspose]
    group
  have hf : fieldAut 3 K (barE h) * dualAut 3 K * fieldAut 3 K σ =
      fieldAut 3 K σ * (fieldAut 3 K (barE h) * dualAut 3 K) := by
    rw [mul_assoc, dualAut_mul_fieldAut, ← mul_assoc, ← map_mul,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K (barE h) σ, map_mul]
    group
  calc fieldAut 3 K (barE h) * dualAut 3 K * (conjAut 3 K A * fieldAut 3 K σ) =
      (fieldAut 3 K (barE h) * dualAut 3 K * conjAut 3 K A) * fieldAut 3 K σ := by group
    _ = conjAut 3 K A * (fieldAut 3 K (barE h) * dualAut 3 K * fieldAut 3 K σ) := by
        rw [hc]; group
    _ = _ := by rw [hf]; group

theorem gammaAut_mul_self : gammaAut h * gammaAut h = 1 := by
  rw [gammaAut]
  calc fieldAut 3 K (barE h) * dualAut 3 K * (fieldAut 3 K (barE h) * dualAut 3 K) =
      fieldAut 3 K (barE h) * (dualAut 3 K * fieldAut 3 K (barE h)) * dualAut 3 K := by group
    _ = 1 := by
        rw [dualAut_mul_fieldAut, ← mul_assoc, ← map_mul, barE_mul_self, map_one, one_mul,
          (standard_automorphism_transport (n := 3) (K := K)).2.2.2.1]

theorem gammaAut_not_mem_semilinear [Finite K] : gammaAut h ∉ semilinearAutGroup 3 K := by
  intro hγ
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (le_refl 3)
  have e : dualAut 3 K = (fieldAut 3 K (barE h))⁻¹ * gammaAut h := by rw [gammaAut]; group
  rw [e]
  exact mul_mem (inv_mem (fieldAut_mem_semilinearAutGroup _)) hγ

theorem mem_range_of_gammaAut_eq (hq3 : p ^ f % 3 = 2) {y : projectiveSL 3 K}
    (hy : gammaAut h y = y) : y ∈ (psuToPSL h).range := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K y
  rw [gammaAut_proj, proj_eq_proj_iff] at hy
  obtain ⟨c, hc3, hc⟩ := hy
  obtain ⟨G, hG⟩ : ∃ G, G = (g : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ Gi, Gi = ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  set θ := Matrix.SpecialLinearGroup.map (barE h : K →+* K) (g⁻¹).transpose with hθ
  have hθm : (θ : Matrix (Fin 3) (Fin 3) K) = (Giᵀ).map h.bar := by
    rw [hθ, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.coe_transpose, ← hGi]
    rfl
  have hGc : G = (c : K) • (Giᵀ).map h.bar := by
    have e : G = (θ : Matrix (Fin 3) (Fin 3) K) *
        ((θ⁻¹ * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left, hG]
    rw [e, hc, hθm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have hbarG : (G.map h.bar)ᵀ = h.bar (c : K) • Gi := by
    rw [hGc]
    ext i j
    simp [h.bar_bar]
  have h1 : (G.map h.bar)ᵀ * G = h.bar (c : K) • 1 := by rw [hbarG, Matrix.smul_mul, hGiG]
  have h3 : G * (G.map h.bar)ᵀ = (c : K) • 1 := by
    have e3 : G * (G.map h.bar)ᵀ = ((c : K) • (Giᵀ).map h.bar) * (G.map h.bar)ᵀ := by
      rw [← hGc]
    rw [e3, Matrix.smul_mul, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.transpose_mul,
      hGGi, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h4 : G * (G.map h.bar)ᵀ = h.bar (c : K) • 1 := by rw [hbarG, Matrix.mul_smul, hGGi]
  have hcc : h.bar (c : K) = c := by
    have := congrFun (congrFun (h4.symm.trans h3) 0) 0
    simpa using this
  have hc1 : (c : K) = 1 := by
    have hpow : h.bar (c : K) = (c : K) ^ 2 := by
      rw [UnitaryFieldData.bar_apply]
      have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 2 := ⟨p ^ f / 3, by omega⟩
      rw [hk, pow_add, pow_mul, hc3', one_pow, one_mul]
    rw [hpow] at hcc
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have : (c : K) * ((c : K) - 1) = 0 := by linear_combination hcc
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
  have hGU : (G.map h.bar)ᵀ * G = 1 := by rw [h1, hcc, hc1, one_smul]
  have hmem : Matrix.SpecialLinearGroup.toGL g ∈ unitarySU p f K 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨g.2, ?_⟩
    change ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1
    rw [← hG]
    exact hGU
  refine ⟨((⟨_, hmem⟩ : unitarySU p f K 3) : unitaryPSU h 3), ?_⟩
  rw [psuToPSL_mk]
  rfl

end UniExt

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
