module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineHeisenberg
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineTrace
public import CFSG.RankThree.SubgroupLists.DicksonGL2

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
  {H : Subgroup (U ≃ₗ[ZMod p] U)} {τ : ZMod p} {η₁ η₂ : U ≃ₗ[ZMod p] U} {c₁ c₂ : U}
  {φ₁ φ₂ : Module.Dual (ZMod p) U}

private def matGram (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) :
    Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![φ₁ c₁, φ₁ c₂; φ₂ c₁, φ₂ c₂]

private def linC (c₁ c₂ : U) : (Fin 2 → ZMod p) →ₗ[ZMod p] U :=
  ∑ j : Fin 2, (LinearMap.proj j).smulRight (![c₁, c₂] j)

private def linPhi (φ₁ φ₂ : Module.Dual (ZMod p) U) : U →ₗ[ZMod p] (Fin 2 → ZMod p) :=
  LinearMap.pi ![φ₁, φ₂]

private lemma linPhi_comp_linC (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) :
    (linPhi φ₁ φ₂).comp (linC c₁ c₂) = (matGram c₁ c₂ φ₁ φ₂).mulVecLin := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [linPhi, linC, matGram, LinearMap.pi_apply, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.vecTail, Fin.succ_zero_eq_one] <;>
    ring

private lemma linPhi_comp_linC_apply (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U)
    (x : Fin 2 → ZMod p) :
    linPhi φ₁ φ₂ (linC c₁ c₂ x) = Matrix.mulVec (matGram c₁ c₂ φ₁ φ₂) x := by
  have h := congrArg (fun f : (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) => f x)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂)
  simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h

private noncomputable def thetaLin (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) : U →ₗ[ZMod p] U :=
  LinearMap.id + C.comp (((N - 1) * G⁻¹).mulVecLin.comp Φ)

private lemma thetaLin_apply (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (v : U) :
    thetaLin C Φ G N v = v + C (Matrix.mulVec ((N - 1) * G⁻¹) (Φ v)) := by
  simp only [thetaLin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Matrix.mulVecLin_apply]

private lemma thetaLin_one (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    thetaLin C Φ G 1 = LinearMap.id := by
  simp [thetaLin]

private lemma one_add_mul_one_add (T T' : U →ₗ[ZMod p] U) :
    (LinearMap.id + T) * (LinearMap.id + T') = LinearMap.id + (T + (T' + T * T')) := by
  rw [show LinearMap.id = (1 : U →ₗ[ZMod p] U) from rfl]
  noncomm_ring

private lemma thetaLin_mul (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det)
    (N N' : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    thetaLin C Φ G N * thetaLin C Φ G N' = thetaLin C Φ G (N * N') := by
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG
  have hGC' : ∀ y : Fin 2 → ZMod p, Φ (C y) = Matrix.mulVec G y := by
    intro y
    have h := congrArg (fun f : (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) => f y) hGC
    simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h
  have key : ∀ M M' : Matrix (Fin 2) (Fin 2) (ZMod p),
      C.comp (M.mulVecLin.comp Φ) * (C.comp (M'.mulVecLin.comp Φ)) =
        C.comp ((M * G * M').mulVecLin.comp Φ) := by
    intro M M'
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply, hGC',
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : ∀ M M' : Matrix (Fin 2) (Fin 2) (ZMod p),
      C.comp (M.mulVecLin.comp Φ) + (C.comp (M'.mulVecLin.comp Φ) +
        C.comp ((M * G * M').mulVecLin.comp Φ)) =
        C.comp ((M + M' + M * G * M').mulVecLin.comp Φ) := by
    intro M M'
    simp only [Matrix.mulVecLin_add, LinearMap.add_comp, LinearMap.comp_add]
    abel
  have hmat : (N - 1) * G⁻¹ + (N' - 1) * G⁻¹ + (N - 1) * G⁻¹ * G * ((N' - 1) * G⁻¹) =
      (N * N' - 1) * G⁻¹ := by
    rw [Matrix.mul_assoc (N - 1) G⁻¹ G, hGinv, Matrix.mul_one,
      ← Matrix.mul_assoc (N - 1) (N' - 1) G⁻¹, ← Matrix.add_mul, ← Matrix.add_mul]
    congr 1
    noncomm_ring
  simp only [thetaLin]
  rw [one_add_mul_one_add, key, hsum, hmat]

private lemma thetaLin_linC (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det)
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (x : Fin 2 → ZMod p) :
    thetaLin C Φ G N (C x) = C (Matrix.mulVec N x) := by
  have hGC' : ∀ y : Fin 2 → ZMod p, Φ (C y) = Matrix.mulVec G y := by
    intro y
    have h := congrArg (fun f : (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) => f y) hGC
    simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG
  have hMG : (N - 1) * G⁻¹ * G = N - 1 := by
    rw [Matrix.mul_assoc, hGinv, Matrix.mul_one]
  have hkey : Matrix.mulVec ((N - 1) * G⁻¹) (Matrix.mulVec G x) =
      Matrix.mulVec (N - 1) x := by
    rw [Matrix.mulVec_mulVec, hMG]
  have hx : x + Matrix.mulVec (N - 1) x = Matrix.mulVec N x := by
    nth_rewrite 1 [← Matrix.one_mulVec (v := x)]
    rw [← Matrix.add_mulVec]
    congr 1
    noncomm_ring
  rw [thetaLin_apply, hGC', hkey, ← map_add, hx]

private lemma thetaLin_A (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₁ : U ≃ₗ[ZMod p] U) (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) :
    thetaLin (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (!![τ, φ₁ c₂; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = (η₁ : U →ₗ[ZMod p] U) := by
  have hA1 : (!![τ, φ₁ c₂; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 =
      !![1, 0; 0, 0] * matGram c₁ c₂ φ₁ φ₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matGram, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
        h₁.1]
  simp only [thetaLin]
  rw [hA1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
  ext v
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Matrix.mulVecLin_apply]
  rw [show (η₁ : U →ₗ[ZMod p] U) v = v + φ₁ v • c₁ from h₁.2 v]
  congr 1
  simp [linC, linPhi, LinearMap.pi_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail,
    Fin.succ_zero_eq_one]

private lemma thetaLin_B (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₂ : U ≃ₗ[ZMod p] U) (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    thetaLin (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (!![1, 0; φ₂ c₁, τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) = (η₂ : U →ₗ[ZMod p] U) := by
  have hB1 : (!![1, 0; φ₂ c₁, τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 =
      !![0, 0; 0, 1] * matGram c₁ c₂ φ₁ φ₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matGram, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
        h₂.1]
  simp only [thetaLin]
  rw [hB1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
  ext v
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Matrix.mulVecLin_apply]
  rw [show (η₂ : U →ₗ[ZMod p] U) v = v + φ₂ v • c₂ from h₂.2 v]
  congr 1
  simp [linC, linPhi, LinearMap.pi_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail,
    Fin.succ_zero_eq_one]

private lemma linC_injective (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U)
    (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det) :
    Function.Injective (linC c₁ c₂ : (Fin 2 → ZMod p) →ₗ[ZMod p] U) := by
  have hGC := linPhi_comp_linC c₁ c₂ φ₁ φ₂
  have hGinv : (matGram c₁ c₂ φ₁ φ₂)⁻¹ * matGram c₁ c₂ φ₁ φ₂ = 1 :=
    Matrix.nonsing_inv_mul _ hG
  intro x y hxy
  have h := congrArg (linPhi φ₁ φ₂) hxy
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hGC, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at h
  have h2 := congrArg (fun z => Matrix.mulVec (matGram c₁ c₂ φ₁ φ₂)⁻¹ z) h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hGinv, Matrix.one_mulVec,
    Matrix.one_mulVec] at h2

private lemma thetaLin_eq_id_iff (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det)
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    thetaLin C Φ G N = LinearMap.id ↔ N = 1 := by
  have hC : Function.Injective C := by
    intro x y hxy
    have h := congrArg Φ hxy
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hGC, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply] at h
    have h2 := congrArg (fun z => Matrix.mulVec G⁻¹ z) h
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
      Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hPhi : Function.Surjective Φ := by
    intro y
    refine ⟨C (Matrix.mulVec G⁻¹ y), ?_⟩
    rw [← LinearMap.comp_apply, hGC, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  constructor
  · intro h
    have hzero : C.comp (((N - 1) * G⁻¹).mulVecLin.comp Φ) = 0 := by
      have := congrArg (fun f : U →ₗ[ZMod p] U => f - LinearMap.id) h
      simpa [thetaLin] using this
    have hM : (N - 1) * G⁻¹ = 0 := by
      have hMv : ∀ y, Matrix.mulVec ((N - 1) * G⁻¹) y = 0 := by
        intro y
        obtain ⟨z, hz⟩ := hPhi y
        have hz' := congrArg (fun f : U →ₗ[ZMod p] U => f z) hzero
        simp only [LinearMap.comp_apply, LinearMap.zero_apply, Matrix.mulVecLin_apply] at hz'
        rw [← hz]
        exact hC (by rw [hz', map_zero])
      ext i j
      have h := congrFun (hMv (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using h
    have h2 : (N - 1) * G⁻¹ * G = 0 := by rw [hM, Matrix.zero_mul]
    rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.mul_one, sub_eq_zero] at h2
  · rintro rfl
    exact thetaLin_one C Φ G

private noncomputable def thetaEquiv (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det)
    (N : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : U ≃ₗ[ZMod p] U :=
  LinearEquiv.ofLinearMap (thetaLin C Φ G (N : Matrix (Fin 2) (Fin 2) (ZMod p)))
    (thetaLin C Φ G ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)))
    (by
      rw [← Module.End.mul_eq_comp, thetaLin_mul C Φ G hGC hG]
      rw [show (N : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 from by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
      exact thetaLin_one C Φ G)
    (by
      rw [← Module.End.mul_eq_comp, thetaLin_mul C Φ G hGC hG]
      rw [show ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (N : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 from by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
      exact thetaLin_one C Φ G)

private noncomputable def Theta (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (U ≃ₗ[ZMod p] U) where
  toFun := thetaEquiv C Φ G hGC hG
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp [thetaEquiv, thetaLin_one]
  map_mul' N N' := by
    apply LinearEquiv.ext
    intro x
    simp only [thetaEquiv, LinearEquiv.coe_ofLinearMap, LinearEquiv.mul_apply]
    exact congrArg (fun f : U →ₗ[ZMod p] U => f x)
      (thetaLin_mul C Φ G hGC hG (N : Matrix (Fin 2) (Fin 2) (ZMod p))
        (N' : Matrix (Fin 2) (Fin 2) (ZMod p))).symm

private lemma isTransvectionLin_conj {t : U ≃ₗ[ZMod p] U} (e : U ≃ₗ[ZMod p] U)
    (h : QTwoLin.IsTransvectionLin t) : QTwoLin.IsTransvectionLin (e * t * e⁻¹) := by
  obtain ⟨u, ψ, hu, hψ, hψu, ht⟩ := h
  refine ⟨e u, ψ.comp (e.symm : U →ₗ[ZMod p] U), ?_, ?_, ?_, fun v => ?_⟩
  · intro h0
    exact hu (by simpa using congrArg e.symm h0)
  · intro h0
    apply hψ
    ext w
    have h1 : (ψ.comp (e.symm : U →ₗ[ZMod p] U)) (e w) = 0 := by simp [h0]
    simpa [LinearMap.comp_apply] using h1
  · simp [LinearMap.comp_apply, hψu]
  · simp [LinearEquiv.mul_apply, ht, LinearMap.comp_apply]

private lemma theta_std_transvection (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det) :
    QTwoLin.IsTransvectionLin (Theta C Φ G hGC hG
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p))
        (by rw [Matrix.det_fin_two_of]; norm_num))) := by
  set t := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p))
    (by rw [Matrix.det_fin_two_of]; norm_num) with htdef
  have ht : (t : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := by rw [htdef]; rfl
  have hcoe : ∀ v : U, (↑(Theta C Φ G hGC hG t) : U →ₗ[ZMod p] U) v =
      thetaLin C Φ G (t : Matrix (Fin 2) (Fin 2) (ZMod p)) v := fun v => rfl
  refine isTransvectionLin_of_sub_mem_span (u := C (![1, 0] : Fin 2 → ZMod p)) ?_ ?_ ?_
  · intro h
    have h1 : thetaLin C Φ G (t : Matrix (Fin 2) (Fin 2) (ZMod p)) = LinearMap.id := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U)) h
      simpa [Theta, thetaEquiv, LinearEquiv.coe_ofLinearMap] using this
    have h2 := (thetaLin_eq_id_iff C Φ G hGC hG
      (t : Matrix (Fin 2) (Fin 2) (ZMod p))).mp h1
    have h3 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by rw [← ht, h2]
    have := congrFun (congrFun h3 0) 1
    simp at this
  · intro v
    rw [show (Theta C Φ G hGC hG t) v =
        (↑(Theta C Φ G hGC hG t) : U →ₗ[ZMod p] U) v from rfl, hcoe v, thetaLin_apply, ht,
      add_sub_cancel_left]
    have h3 : Matrix.mulVec (((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) *
        G⁻¹) (Φ v) = (Matrix.mulVec G⁻¹ (Φ v)) 1 • (![1, 0] : Fin 2 → ZMod p) := by
      rw [show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 = !![0, 1; 0, 0] from by
        ext i j; fin_cases i <;> fin_cases j <;> simp]
      rw [← Matrix.mulVec_mulVec]
      ext i; fin_cases i <;> simp [Matrix.mulVec]
    rw [h3, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [show (Theta C Φ G hGC hG t) (C (![1, 0] : Fin 2 → ZMod p)) =
        (↑(Theta C Φ G hGC hG t) : U →ₗ[ZMod p] U) (C (![1, 0] : Fin 2 → ZMod p)) from rfl,
      hcoe (C (![1, 0] : Fin 2 → ZMod p)),
      thetaLin_linC C Φ G hGC hG (t : Matrix (Fin 2) (Fin 2) (ZMod p))
        (![1, 0] : Fin 2 → ZMod p), ht,
      show Matrix.mulVec (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p))
        (![1, 0] : Fin 2 → ZMod p) = (![1, 0] : Fin 2 → ZMod p) from by
        ext i; fin_cases i <;> simp [Matrix.mulVec]]

private lemma theta_transvection (C : (Fin 2 → ZMod p) →ₗ[ZMod p] U)
    (Φ : U →ₗ[ZMod p] (Fin 2 → ZMod p)) (G : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hGC : Φ.comp C = G.mulVecLin) (hG : IsUnit G.det)
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} (hg : g ≠ 1) (hgp : g ^ p = 1) :
    QTwoLin.IsTransvectionLin (Theta C Φ G hGC hG g) := by
  obtain ⟨k, hk⟩ := CFSG.RankThree.SubgroupLists.exists_conj_transvection g hgp hg
  set t := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p))
    (by rw [Matrix.det_fin_two_of]; norm_num) with htdef
  have ht : (t : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := by rw [htdef]; rfl
  have hkg : g * k = k * t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht]
    exact hk
  have hconj : g = k * t * k⁻¹ := by
    calc g = g * k * k⁻¹ := by group
      _ = k * t * k⁻¹ := by rw [hkg]
  rw [hconj, map_mul, map_mul, map_inv]
  exact isTransvectionLin_conj (Theta C Φ G hGC hG k) (theta_std_transvection C Φ G hGC hG)

private noncomputable def planeA (τ b : ZMod p) (hτ : τ ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![τ, b; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p))
    (by rw [Matrix.det_fin_two_of]; simpa using hτ)

private noncomputable def planeB (τ b' : ZMod p) (hτ : τ ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![1, 0; b', τ] : Matrix (Fin 2) (Fin 2) (ZMod p))
    (by rw [Matrix.det_fin_two_of]; simpa using hτ)

private lemma planeA_coe (τ b : ZMod p) (hτ : τ ≠ 0) :
    (planeA τ b hτ : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1] := by
  simp [planeA, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private lemma planeB_coe (τ b' : ZMod p) (hτ : τ ≠ 0) :
    (planeB τ b' hτ : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ] := by
  simp [planeB, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private lemma Theta_planeA (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₁ : U ≃ₗ[ZMod p] U) (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) :
    Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (planeA τ (φ₁ c₂) h₁.type_ne_zero) = η₁ := by
  apply LinearEquiv.ext
  intro v
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f v)
    (thetaLin_A c₁ c₂ φ₁ φ₂ τ η₁ hG h₁)
  simpa [Theta, thetaEquiv, LinearEquiv.coe_ofLinearMap, planeA_coe] using h

private lemma Theta_planeB (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₂ : U ≃ₗ[ZMod p] U) (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (planeB τ (φ₂ c₁) h₂.type_ne_zero) = η₂ := by
  apply LinearEquiv.ext
  intro v
  have h := congrArg (fun f : U →ₗ[ZMod p] U => f v)
    (thetaLin_B c₁ c₂ φ₁ φ₂ τ η₂ hG h₂)
  simpa [Theta, thetaEquiv, LinearEquiv.coe_ofLinearMap, planeB_coe] using h

private lemma plane_hpf (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₁ η₂ : U ≃ₗ[ZMod p] U) (H : Subgroup (U ≃ₗ[ZMod p] U))
    (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, φ₁ c₂; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; φ₂ c₁, τ])
    (hAeq : Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG A = η₁)
    (hBeq : Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG B = η₂)
    (htv : QTwoLin.TransvectionFree H) (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) :
    ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1 := by
  intro g hg hgp
  by_contra hg1
  set T := Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG with hTdef
  have hmem : T g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)) := by
    have hsub : Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) ≤
        Subgroup.comap T (Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · change T x ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))
        rw [hTdef, hAeq]
        exact Subgroup.subset_closure (Or.inl rfl)
      · change T x ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))
        rw [hTdef, hBeq]
        exact Subgroup.subset_closure (Or.inr rfl)
    exact hsub hg
  have hle : Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hη₁
    · exact hη₂
  exact (htv (T g) (hle hmem)) (hTdef ▸ theta_transvection (linC c₁ c₂) (linPhi φ₁ φ₂)
    (matGram c₁ c₂ φ₁ φ₂) (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG hg1 hgp)

private lemma planeA_hpf (c₁ c₂ : U) (φ₁ φ₂ : Module.Dual (ZMod p) U) (τ : ZMod p)
    (η₁ η₂ : U ≃ₗ[ZMod p] U) (H : Subgroup (U ≃ₗ[ZMod p] U))
    (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (htv : QTwoLin.TransvectionFree H) (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    ∀ g ∈ Subgroup.closure ({planeA τ (φ₁ c₂) h₁.type_ne_zero,
      planeB τ (φ₂ c₁) h₂.type_ne_zero} :
        Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))), g ^ p = 1 → g = 1 :=
  plane_hpf c₁ c₂ φ₁ φ₂ τ η₁ η₂ H hG _ _
    (planeA_coe τ (φ₁ c₂) h₁.type_ne_zero)
    (planeB_coe τ (φ₂ c₁) h₂.type_ne_zero)
    (Theta_planeA c₁ c₂ φ₁ φ₂ τ η₁ hG h₁) (Theta_planeB c₁ c₂ φ₁ φ₂ τ η₂ hG h₂)
    htv hη₁ hη₂

theorem orderOf_eq_four_or_five_of_not_commute (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : 4 ≤ orderOf τ) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    orderOf τ = 4 ∨ orderOf τ = 5 := by
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hτ; omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨-, hb, hb', hq⟩ := linked_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ2 hcomm
  have hGdet : (matGram c₁ c₂ φ₁ φ₂).det = (τ - 1) ^ 2 - φ₁ c₂ * φ₂ c₁ := by
    rw [Matrix.det_fin_two]
    simp only [matGram, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]
    rw [h₁.1, h₂.1]
    ring
  have hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det := by
    rw [hGdet]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hq.symm)
  exact orderOf_eq_four_or_five_of_planePair (planeA_coe τ (φ₁ c₂) h₁.type_ne_zero)
    (planeB_coe τ (φ₂ c₁) h₂.type_ne_zero) hb hb'
    (planeA_hpf c₁ c₂ φ₁ φ₂ τ η₁ η₂ H hG htv hη₁ hη₂ h₁ h₂) hτ

theorem apply_mul_apply_eq_of_not_commute_four (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : orderOf τ = 4) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    φ₁ c₂ * φ₂ c₁ = -τ := by
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hτ; omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨-, hb, hb', hq⟩ := linked_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ2 hcomm
  have hGdet : (matGram c₁ c₂ φ₁ φ₂).det = (τ - 1) ^ 2 - φ₁ c₂ * φ₂ c₁ := by
    rw [Matrix.det_fin_two]
    simp only [matGram, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]
    rw [h₁.1, h₂.1]
    ring
  have hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det := by
    rw [hGdet]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hq.symm)
  exact mul_eq_neg_of_planePair_four (planeA_coe τ (φ₁ c₂) h₁.type_ne_zero)
    (planeB_coe τ (φ₂ c₁) h₂.type_ne_zero) hb hb'
    (planeA_hpf c₁ c₂ φ₁ φ₂ τ η₁ η₂ H hG htv hη₁ hη₂ h₁ h₂) hτ

theorem apply_mul_apply_eq_of_not_commute_five (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : orderOf τ = 5) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    φ₁ c₂ * φ₂ c₁ = -τ ∨ φ₁ c₂ * φ₂ c₁ = τ ^ 2 - τ + 1 := by
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hτ; omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨-, hb, hb', hq⟩ := linked_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ2 hcomm
  have hGdet : (matGram c₁ c₂ φ₁ φ₂).det = (τ - 1) ^ 2 - φ₁ c₂ * φ₂ c₁ := by
    rw [Matrix.det_fin_two]
    simp only [matGram, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]
    rw [h₁.1, h₂.1]
    ring
  have hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det := by
    rw [hGdet]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hq.symm)
  exact mul_eq_of_planePair_five (planeA_coe τ (φ₁ c₂) h₁.type_ne_zero)
    (planeB_coe τ (φ₂ c₁) h₂.type_ne_zero) hb hb'
    (planeA_hpf c₁ c₂ φ₁ φ₂ τ η₁ η₂ H hG htv hη₁ hη₂ h₁ h₂) hτ

private lemma linC_pair (c₁ c₂ : U) (x y : ZMod p) :
    linC c₁ c₂ (![x, y] : Fin 2 → ZMod p) = x • c₁ + y • c₂ := by
  simp [linC, Fin.sum_univ_two]

private lemma linC_mem (c₁ c₂ : U) (w : Fin 2 → ZMod p) :
    linC c₁ c₂ w ∈ Submodule.span (ZMod p) {c₁, c₂} := by
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  exact Submodule.mem_span_pair.mpr ⟨w 0, w 1, by rw [linC_pair]⟩

private lemma zs19f_closure_fix (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    ∀ g ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)),
      ∀ v, φ₁ v = 0 → φ₂ v = 0 → g v = v := by
  intro g hg
  let K : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ∀ v, φ₁ v = 0 → φ₂ v = 0 → g v = v}
      mul_mem' := by
        intro x y hx hy v hv1 hv2
        rw [LinearEquiv.mul_apply, hy v hv1 hv2]
        exact hx v hv1 hv2
      one_mem' := by intro v _ _; rfl
      inv_mem' := by
        intro x hx v hv1 hv2
        have hxv : x v = v := hx v hv1 hv2
        change x.symm v = v
        rw [← hxv, LinearEquiv.symm_apply_apply]
        exact hxv.symm }
  have hK : Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl) v hv1 hv2
    · exact h₁.apply_of_apply_eq_zero hv1
    · exact h₂.apply_of_apply_eq_zero hv2
  have hgK : ∀ v, φ₁ v = 0 → φ₂ v = 0 → g v = v := hK hg
  exact hgK

private lemma zs19f_closure_le (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) (h₂ : IsHomologyWith τ η₂ c₂ φ₂) :
    Subgroup.closure ({planeA τ (φ₁ c₂) h₁.type_ne_zero, planeB τ (φ₂ c₁) h₂.type_ne_zero} :
        Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) ≤
      Subgroup.comap (Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG)
        (Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · change Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (planeA τ (φ₁ c₂) h₁.type_ne_zero) ∈
      Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))
    rw [Theta_planeA c₁ c₂ φ₁ φ₂ τ η₁ hG h₁]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · change Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (planeB τ (φ₂ c₁) h₂.type_ne_zero) ∈
      Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U))
    rw [Theta_planeB c₁ c₂ φ₁ φ₂ τ η₂ hG h₂]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private lemma zs19f_theta_apply (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (m : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (w : Fin 2 → ZMod p) :
    (Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG m) (linC c₁ c₂ w) =
      linC c₁ c₂ (Matrix.mulVec (m : Matrix (Fin 2) (Fin 2) (ZMod p)) w) := by
  change thetaLin (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (m : Matrix (Fin 2) (Fin 2) (ZMod p)) (linC c₁ c₂ w) = _
  exact thetaLin_linC (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (m : Matrix (Fin 2) (Fin 2) (ZMod p)) w

private lemma zs19f_eta_plane (hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det)
    (k A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hk_eq : ((k * A * k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹)
    (w : Fin 2 → ZMod p) :
    (Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (k * A * k⁻¹)) (linC c₁ c₂ w) =
      linC c₁ c₂ (Matrix.mulVec (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w) := by
  change thetaLin (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      ((k * A * k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) (linC c₁ c₂ w) = _
  rw [hk_eq]
  exact thetaLin_linC (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w

private lemma zs19f_Ainv (hτ0 : τ ≠ 0) {A : Matrix (Fin 2) (Fin 2) (ZMod p)}
    {w : Fin 2 → ZMod p} (h : Matrix.mulVec (τ • A) w = τ • w) :
    Matrix.mulVec A w = w := by
  rw [Matrix.smul_mulVec] at h
  have := congrArg (fun z => τ⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hτ0, one_smul] using this

private lemma zs19f_Aw (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hAunit : IsUnit (A : Matrix (Fin 2) (Fin 2) (ZMod p)).det) {w : Fin 2 → ZMod p}
    (h : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹ w = w) :
    Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p)) w = w := by
  calc Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p)) w
      = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p))
          (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹ w) := by rw [h]
    _ = Matrix.mulVec ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) w := by
          rw [Matrix.mul_nonsing_inv _ hAunit]
    _ = w := by rw [Matrix.one_mulVec]

private lemma zs19f_row (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hAcoe : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, φ₁ c₂; 0, 1])
    (h₁ : IsHomologyWith τ η₁ c₁ φ₁) {w : Fin 2 → ZMod p}
    (hAw : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p)) w = w) :
    Matrix.mulVec (matGram c₁ c₂ φ₁ φ₂) w 0 = 0 := by
  have hsub : Matrix.mulVec ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) w = 0 := by
    rw [Matrix.sub_mulVec, hAw, Matrix.one_mulVec, sub_self]
  have hrowfun : ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) 0 =
      matGram c₁ c₂ φ₁ φ₂ 0 := by
    rw [hAcoe]
    ext j; fin_cases j <;>
      simp [Matrix.sub_apply, matGram, Matrix.cons_val_zero,
        Matrix.cons_val_one, h₁.1]
  have hrow : Matrix.mulVec ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) w 0 =
      Matrix.mulVec (matGram c₁ c₂ φ₁ φ₂) w 0 := by
    show ((A : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) 0 ⬝ᵥ w = matGram c₁ c₂ φ₁ φ₂ 0 ⬝ᵥ w
    rw [hrowfun]
  rw [← hrow, hsub]
  rfl

theorem exists_dual_homology_of_not_commute (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : 4 ≤ orderOf τ) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    ∃ η ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)),
      ∃ (c : U) (φ : Module.Dual (ZMod p) U), IsHomologyWith τ η c φ ∧
        c ∈ Submodule.span (ZMod p) {c₁, c₂} ∧ φ₁ c = 0 ∧ φ c₁ = 0 ∧
          ∀ v, φ₁ v = 0 → φ₂ v = 0 → φ v = 0 := by
  have hτ1 : τ ≠ 1 := by intro h; rw [h, orderOf_one] at hτ; omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨-, hb, hb', hq⟩ := linked_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ2 hcomm
  have hGdet : (matGram c₁ c₂ φ₁ φ₂).det = (τ - 1) ^ 2 - φ₁ c₂ * φ₂ c₁ := by
    rw [Matrix.det_fin_two]
    simp only [matGram, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]
    rw [h₁.1, h₂.1]
    ring
  have hG : IsUnit (matGram c₁ c₂ φ₁ φ₂).det := by
    rw [hGdet]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hq.symm)
  have hpf := planeA_hpf c₁ c₂ φ₁ φ₂ τ η₁ η₂ H hG htv hη₁ hη₂ h₁ h₂
  obtain ⟨k, hk_mem, hk_eq⟩ := exists_conj_eq_smul_inv_of_planePair
    (planeA_coe τ (φ₁ c₂) h₁.type_ne_zero) (planeB_coe τ (φ₂ c₁) h₂.type_ne_zero)
    hb hb' hpf hτ
  let A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) := planeA τ (φ₁ c₂) h₁.type_ne_zero
  have hAcoe : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, φ₁ c₂; 0, 1] :=
    planeA_coe τ (φ₁ c₂) h₁.type_ne_zero
  have hAunit : IsUnit (A : Matrix (Fin 2) (Fin 2) (ZMod p)).det := by
    rw [hAcoe, Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.mpr (by simpa using h₁.type_ne_zero)
  have hMinv : (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) = !![1, -φ₁ c₂; 0, τ] := by
    have hmul : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, -φ₁ c₂; 0, τ] =
        τ • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [hAcoe]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    have hAinv : (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹ =
        τ⁻¹ • (!![1, -φ₁ c₂; 0, τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.mul_smul, hmul, smul_smul, inv_mul_cancel₀ h₁.type_ne_zero, one_smul]
    rw [hAinv, smul_smul, mul_inv_cancel₀ h₁.type_ne_zero, one_smul]
  let k' : U ≃ₗ[ZMod p] U := Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG k
  have hk'_mem : k' ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)) :=
    zs19f_closure_le hG h₁ h₂ hk_mem
  let η : U ≃ₗ[ZMod p] U := Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
    (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (k * A * k⁻¹)
  have heta_eq : η = k' * η₁ * k'⁻¹ := by
    change Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG (k * A * k⁻¹) =
      Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
        (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG k * η₁ * _⁻¹
    rw [map_mul, map_mul, map_inv]
    congr 2
    rw [show A = planeA τ (φ₁ c₂) h₁.type_ne_zero from rfl]
    exact Theta_planeA c₁ c₂ φ₁ φ₂ τ η₁ hG h₁
  let c : U := k' c₁
  let φ : Module.Dual (ZMod p) U := φ₁ ∘ₗ (k'.symm : U →ₗ[ZMod p] U)
  have hisHom : IsHomologyWith τ η c φ := by rw [heta_eq]; exact h₁.conj k'
  have hη_mem : η ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)) :=
    zs19f_closure_le hG h₁ h₂ (mul_mem (mul_mem hk_mem
      (Subgroup.subset_closure (Set.mem_insert _ _))) (inv_mem hk_mem))
  have heta_plane : ∀ w : Fin 2 → ZMod p, η (linC c₁ c₂ w) =
      linC c₁ c₂ (Matrix.mulVec (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w) := by
    intro w
    have hk' : ((k * A * k⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹ := by
      show ((k * planeA τ (φ₁ c₂) h₁.type_ne_zero * k⁻¹ :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        τ • (planeA τ (φ₁ c₂) h₁.type_ne_zero : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using hk_eq
    exact zs19f_eta_plane hG k A hk' w
  have hc_eq : c = linC c₁ c₂ (Matrix.mulVec (k : Matrix (Fin 2) (Fin 2) (ZMod p))
      (![1, 0] : Fin 2 → ZMod p)) := by
    have h1 : c₁ = linC c₁ c₂ (![1, 0] : Fin 2 → ZMod p) := by
      rw [linC_pair, one_smul, zero_smul, add_zero]
    change (Theta (linC c₁ c₂) (linPhi φ₁ φ₂) (matGram c₁ c₂ φ₁ φ₂)
      (linPhi_comp_linC c₁ c₂ φ₁ φ₂) hG k : U →ₗ[ZMod p] U) c₁ = _
    conv_lhs => arg 2; rw [h1]
    exact zs19f_theta_apply hG k (![1, 0] : Fin 2 → ZMod p)
  have hcmem : c ∈ Submodule.span (ZMod p) {c₁, c₂} := by
    rw [hc_eq]; exact linC_mem c₁ c₂ _
  have hc0 : c ≠ 0 := by
    intro h
    have h' : k' c₁ = 0 := h
    have : c₁ = 0 := by
      simpa using congrArg (fun x => (k'⁻¹ : U ≃ₗ[ZMod p] U) x) h'
    exact h₁.centre_ne_zero hτ1 this
  have hφc1 : φ c₁ = 0 := by
    have h1 : η c₁ = c₁ := by
      have h := heta_plane (![1, 0] : Fin 2 → ZMod p)
      rw [linC_pair] at h
      rw [show Matrix.mulVec (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹)
          (![1, 0] : Fin 2 → ZMod p) = (![1, 0] : Fin 2 → ZMod p) from by
            rw [hMinv]
            ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
              Matrix.cons_val_zero, Matrix.cons_val_one], linC_pair, one_smul, zero_smul,
        add_zero] at h
      exact h
    have h2 : η c₁ = c₁ + φ c₁ • c := hisHom.2 c₁
    rw [h1] at h2
    have hzero : φ c₁ • c = 0 := by
      have h2' : c₁ + φ c₁ • c = c₁ + 0 := by rw [← h2, add_zero]
      exact add_left_cancel h2'
    exact (smul_eq_zero.mp hzero).resolve_right hc0
  have hφ1c : φ₁ c = 0 := by
    obtain ⟨w, hw⟩ : ∃ w, c = linC c₁ c₂ w := ⟨_, hc_eq⟩
    have h1 : η (linC c₁ c₂ w) =
        linC c₁ c₂ (Matrix.mulVec (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w) :=
      heta_plane w
    have h2 : η (linC c₁ c₂ w) = τ • linC c₁ c₂ w := by rw [← hw]; exact hisHom.apply_centre
    rw [h1, ← map_smul] at h2
    have hw_eq : Matrix.mulVec (τ • (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹) w = τ • w :=
      linC_injective c₁ c₂ φ₁ φ₂ hG h2
    have hAinvw : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p))⁻¹ w = w :=
      zs19f_Ainv h₁.type_ne_zero hw_eq
    have hAw : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod p)) w = w :=
      zs19f_Aw A hAunit hAinvw
    have hφ1 : φ₁ (linC c₁ c₂ w) = Matrix.mulVec (matGram c₁ c₂ φ₁ φ₂) w 0 := by
      have := congrArg (fun f : Fin 2 → ZMod p => f 0)
        (linPhi_comp_linC_apply c₁ c₂ φ₁ φ₂ w)
      simpa [linPhi, LinearMap.pi_apply] using this
    rw [hw, hφ1]
    exact zs19f_row A hAcoe h₁ hAw
  have hφY : ∀ v, φ₁ v = 0 → φ₂ v = 0 → φ v = 0 := by
    intro v hv1 hv2
    change φ₁ ((k'⁻¹ : U ≃ₗ[ZMod p] U) v) = 0
    rw [zs19f_closure_fix h₁ h₂ (k'⁻¹) (inv_mem hk'_mem) v hv1 hv2]
    exact hv1
  exact ⟨η, hη_mem, c, φ, hisHom, hcmem, hφ1c, hφc1, hφY⟩

theorem exists_eq_smul_on_span_of_not_commute (htv : QTwoLin.TransvectionFree H)
    (hη₁ : η₁ ∈ H) (hη₂ : η₂ ∈ H) (h₁ : IsHomologyWith τ η₁ c₁ φ₁)
    (h₂ : IsHomologyWith τ η₂ c₂ φ₂) (hτ : 4 ≤ orderOf τ) (hcomm : η₁ * η₂ ≠ η₂ * η₁) :
    ∃ ψ ∈ Subgroup.closure ({η₁, η₂} : Set (U ≃ₗ[ZMod p] U)),
      (∀ v ∈ Submodule.span (ZMod p) {c₁, c₂}, ψ v = τ • v) ∧
        ∀ v, φ₁ v = 0 → φ₂ v = 0 → ψ v = v := by
  have hτ1 : τ ≠ 1 := by intro h; rw [h, orderOf_one] at hτ; omega
  obtain ⟨η, hη_mem, c, φ, hisHom, hcmem, hφ1c, hφc1, hφY⟩ :=
    exists_dual_homology_of_not_commute htv hη₁ hη₂ h₁ h₂ hτ hcomm
  refine ⟨η₁ * η, mul_mem (Subgroup.subset_closure (Set.mem_insert _ _)) hη_mem, ?_, ?_⟩
  · obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hcmem
    have hc0 : c ≠ 0 := hisHom.centre_ne_zero hτ1
    have hβ0 : β ≠ 0 := by
      intro hβ
      rw [hβ, zero_smul, add_zero] at hαβ
      have hα : α = 0 := by
        have h := congrArg φ₁ hαβ
        rw [map_smul, h₁.1, hφ1c, smul_eq_zero] at h
        rcases h with h | h
        · exact h
        · exact absurd h (sub_ne_zero.mpr hτ1)
      rw [hα, zero_smul] at hαβ
      exact hc0 hαβ.symm
    have hψ_c1 : (η₁ * η) c₁ = τ • c₁ := by
      change η₁ (η c₁) = τ • c₁
      have h : η c₁ = c₁ := by rw [hisHom.2, hφc1, zero_smul, add_zero]
      rw [h, h₁.apply_centre]
    have hψ_c : (η₁ * η) c = τ • c := by
      change η₁ (η c) = τ • c
      rw [hisHom.apply_centre, map_smul]
      congr 1
      rw [h₁.2, hφ1c, zero_smul, add_zero]
    have hle : Submodule.span (ZMod p) {c₁, c₂} ≤ Submodule.span (ZMod p) {c₁, c} := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · refine Submodule.mem_span_pair.mpr ⟨-(β⁻¹ * α), β⁻¹, ?_⟩
        rw [← hαβ]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul, neg_smul,
          ← add_assoc, neg_add_cancel, zero_add]
    intro v hv
    have hv' : v ∈ Submodule.span (ZMod p) {c₁, c} := hle hv
    obtain ⟨a, d, had⟩ := Submodule.mem_span_pair.mp hv'
    rw [← had, map_add, map_smul, map_smul, hψ_c1, hψ_c, smul_comm a τ c₁,
      smul_comm d τ c, smul_add]
  · intro v hv1 hv2
    change η₁ (η v) = v
    have h : η v = v := by rw [hisHom.2, hφY v hv1 hv2, zero_smul, add_zero]
    rw [h]
    exact h₁.apply_of_apply_eq_zero hv1

end CFSG.StandardType.ZS

end
