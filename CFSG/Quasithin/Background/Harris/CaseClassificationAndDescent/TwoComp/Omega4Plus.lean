module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidOmegaFour
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.NaturalEndField
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ComponentClassification.RankTwoClassical.ORigid
open CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped MatrixGroups Matrix

section Theta

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def thetaHom : SL(2, K) × SL(2, K) →* GL (Fin 2 ⊕ Fin 2) K :=
  MonoidHom.noncommCoprod (rhoOneMat (K := K)).toHomUnits (rhoTwoMat (K := K)).toHomUnits
    (fun a b => Units.ext (by
      simp only [Units.val_mul, MonoidHom.coe_toHomUnits]
      exact rhoOne_mul_rhoTwo b a))

theorem thetaHom_apply (x : SL(2, K) × SL(2, K)) :
    thetaHom x = (rhoOneMat (K := K)).toHomUnits x.1 * (rhoTwoMat (K := K)).toHomUnits x.2 :=
  MonoidHom.noncommCoprod_apply _ _ _ x

theorem thetaHom_val (a b : SL(2, K)) :
    ((thetaHom (a, b) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      rhoOneMat a * rhoTwoMat b := by
  rw [thetaHom_apply]
  simp

theorem oMat_thetaHom (a b : SL(2, K)) (v : Fin 2 ⊕ Fin 2 → K) :
    oMat K (((thetaHom (a, b) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      (a : Matrix (Fin 2) (Fin 2) K) * oMat K v * (b : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [thetaHom_val, ← Matrix.mulVec_mulVec, rhoOneMat_eq_shape, oMat_rhoOneShape, oMat_rhoTwoMat,
    Matrix.mul_assoc]

theorem thetaHom_mem [Finite K] (h4 : 4 ≤ Nat.card K) (x : SL(2, K) × SL(2, K)) :
    thetaHom x ∈ StatedOmega (StatedQuadPlus 2 K) := by
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_four h4)).commutator_eq_top
  have h1 : (rhoOneMat (K := K)).toHomUnits x.1 ∈ StatedOmega (StatedQuadPlus 2 K) :=
    mem_statedOmega_of_perfect hSL (rhoOneMat (K := K)).toHomUnits
      (fun B' => Subgroup.subset_closure fun v => by
        simp only [MonoidHom.coe_toHomUnits]
        exact quadPlus_two_rhoOne B' v) x.1
  have h2 : (rhoTwoMat (K := K)).toHomUnits x.2 ∈ StatedOmega (StatedQuadPlus 2 K) :=
    mem_statedOmega_of_perfect hSL (rhoTwoMat (K := K)).toHomUnits
      (fun A' => Subgroup.subset_closure fun v => by
        simp only [MonoidHom.coe_toHomUnits]
        exact quadPlus_two_rhoTwo A' v) x.2
  rw [thetaHom_apply]
  exact Subgroup.mul_mem _ h1 h2

theorem thetaHom_surj [Finite K] {Y : GL (Fin 2 ⊕ Fin 2) K}
    (hY : Y ∈ StatedOmega (StatedQuadPlus 2 K)) : ∃ x, thetaHom x = Y := by
  obtain ⟨A, B, h⟩ := exists_rho_of_mem_statedOmega_quadPlus_two hY
  exact ⟨(A, B), Units.ext (by rw [thetaHom_val]; exact h.symm)⟩

omit [CharP K 2] in
theorem exists_scalar_of_commute_two {C : Matrix (Fin 2) (Fin 2) K}
    (h1 : Matrix.single 0 1 (1 : K) * C = C * Matrix.single 0 1 1)
    (h2 : Matrix.single 1 0 (1 : K) * C = C * Matrix.single 1 0 1) :
    ∃ c : K, C = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨C 0 0, ?_⟩
  have a1 := congrFun (congrFun h1 0) 0
  have a2 := congrFun (congrFun h1 1) 1
  have a3 := congrFun (congrFun h2 0) 0
  have a4 := congrFun (congrFun h2 1) 1
  have a5 := congrFun (congrFun h1 0) 1
  have a6 := congrFun (congrFun h2 1) 0
  simp [Matrix.mul_apply, Matrix.single_apply] at a1 a2 a3 a4 a5 a6
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem thetaHom_injective : Function.Injective (thetaHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  have hv : ∀ M : Matrix (Fin 2) (Fin 2) K,
      (a : Matrix (Fin 2) (Fin 2) K) * M * (b : Matrix (Fin 2) (Fin 2) K)ᵀ = M := by
    intro M
    have := oMat_thetaHom a b ((oMat K).symm M)
    rw [h, Units.val_one, Matrix.one_mulVec, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hab : (a : Matrix (Fin 2) (Fin 2) K) * (b : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    simpa using hv 1
  have hba : (b : Matrix (Fin 2) (Fin 2) K)ᵀ * (a : Matrix (Fin 2) (Fin 2) K) = 1 :=
    mul_eq_one_comm.mp hab
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) K,
      (a : Matrix (Fin 2) (Fin 2) K) * M = M * (a : Matrix (Fin 2) (Fin 2) K) := by
    intro M
    have := congrArg (fun N => N * (a : Matrix (Fin 2) (Fin 2) K)) (hv M)
    simp only [Matrix.mul_assoc, hba, Matrix.mul_one] at this
    exact this
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_two (hcomm (Matrix.single 0 1 1)).symm (hcomm (Matrix.single 1 0 1)).symm
  have hdet := a.2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have hc1 : c = 1 := by
    have : (c - 1) ^ 2 = 0 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      simp only [Fintype.card_fin] at hdet
      linear_combination hdet + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)
  have ha1 : a = 1 := Subtype.ext (by rw [hc, hc1, one_smul]; rfl)
  have hb : (b : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    have := hba
    rwa [ha1, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] at this
  have hb1 : b = 1 := Subtype.ext (by
    have := congrArg Matrix.transpose hb
    simpa using this)
  rw [ha1, hb1]
  rfl

end Theta

section Natural

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {K : Type} [Field K] [Algebra (ZMod 2) K]

@[expose] noncomputable def coordEquiv (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) :
    V ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 → K) :=
  ψ.trans ((oMat K).symm.restrictScalars (ZMod 2))

theorem coordEquiv_apply (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) (v : V) :
    coordEquiv ψ v = (oMat K).symm (ψ v) := rfl

theorem coordEquiv_symm_apply (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (w : Fin 2 ⊕ Fin 2 → K) : (coordEquiv ψ).symm w = ψ.symm (oMat K w) := rfl

theorem exists_mulEquiv_omega_of_tensor [Finite K] (h4 : 4 ≤ Nat.card K)
    {H : Subgroup (GLV V)} (φ : ↥H ≃* SL(2, K) × SL(2, K))
    (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
      ((φ γ).1 : Matrix (Fin 2) (Fin 2) K) * ψ v * ((φ γ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ) :
    ∃ φ' : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 K)), ∀ (γ : ↥H) (v : V),
      coordEquiv ψ ((γ : GLV V) v) =
        ((φ' γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          coordEquiv ψ v := by
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let f : ↥H →* GL (Fin 2 ⊕ Fin 2) K := thetaHom.comp φ.toMonoidHom
  let g : ↥H →* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    f.codRestrict _ fun γ => thetaHom_mem h4 (φ γ)
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => φ.injective (thetaHom_injective (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨Y, hY⟩
    obtain ⟨x, hx⟩ := thetaHom_surj hY
    exact ⟨φ.symm x, Subtype.ext (by simp [g, f, hx])⟩
  refine ⟨MulEquiv.ofBijective g hg, fun γ v => ?_⟩
  apply (oMat K).injective
  have h1 : ((MulEquiv.ofBijective g hg γ : ↥(StatedOmega (StatedQuadPlus 2 K))) :
      GL (Fin 2 ⊕ Fin 2) K) = thetaHom (φ γ) := rfl
  rw [h1]
  have := oMat_thetaHom (φ γ).1 (φ γ).2 (coordEquiv ψ v)
  rw [Prod.mk.eta] at this
  rw [this, coordEquiv_apply, coordEquiv_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, hψ]

end Natural

section Commutant

variable {K : Type} [Field K] [Algebra (ZMod 2) K]

omit [Algebra (ZMod 2) K] in
@[expose] noncomputable def transSL (i j : Fin 2) (hij : i ≠ j) (a : K) : SL(2, K) :=
  ⟨Matrix.transvection i j a, Matrix.det_transvection_of_ne i j hij a⟩

omit [Algebra (ZMod 2) K] in
theorem transSL_coe (i j : Fin 2) (hij : i ≠ j) (a : K) :
    (transSL i j hij a : Matrix (Fin 2) (Fin 2) K) = 1 + Matrix.single i j a := rfl

theorem exists_scalar_of_commute_tensor (F : Module.End (ZMod 2) (Matrix (Fin 2) (Fin 2) K))
    (hF : ∀ g h : SL(2, K), ∀ X : Matrix (Fin 2) (Fin 2) K,
      F ((g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) =
        (g : Matrix (Fin 2) (Fin 2) K) * F X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) :
    ∃ c : K, ∀ X, F X = c • X := by
  have hl : ∀ i j (hij : i ≠ j) (a : K) (X : Matrix (Fin 2) (Fin 2) K),
      F (Matrix.single i j a * X) = Matrix.single i j a * F X := by
    intro i j hij a X
    have h := hF (transSL i j hij a) 1 X
    simp only [transSL_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, map_add] at h
    exact add_left_cancel h
  have hadd : ∀ M N : Matrix (Fin 2) (Fin 2) K, (∀ X, F (M * X) = M * F X) →
      (∀ X, F (N * X) = N * F X) → ∀ X, F ((M + N) * X) = (M + N) * F X := by
    intro M N hM hN X
    rw [Matrix.add_mul, map_add, hM, hN, Matrix.add_mul]
  have hmul : ∀ M N : Matrix (Fin 2) (Fin 2) K, (∀ X, F (M * X) = M * F X) →
      (∀ X, F (N * X) = N * F X) → ∀ X, F ((M * N) * X) = (M * N) * F X := by
    intro M N hM hN X
    rw [Matrix.mul_assoc, hM, hN, Matrix.mul_assoc]
  have hsingle : ∀ i j (a : K), ∀ X, F (Matrix.single i j a * X) = Matrix.single i j a * F X := by
    intro i j a
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ≠ i := by
        fin_cases i
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
      have : Matrix.single i i a = Matrix.single i k a * Matrix.single k i 1 := by
        rw [Matrix.single_mul_single_same, mul_one]
      rw [this]
      exact hmul _ _ (hl i k (Ne.symm hk) a) (hl k i hk 1)
    · exact hl i j hij a
  have hall : ∀ M : Matrix (Fin 2) (Fin 2) K, ∀ X, F (M * X) = M * F X := by
    intro M
    rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_induction _ (fun N : Matrix (Fin 2) (Fin 2) K => ∀ X, F (N * X) = N * F X)
      hadd (by intro X; simp) fun i _ => ?_
    refine Finset.sum_induction _ (fun N : Matrix (Fin 2) (Fin 2) K => ∀ X, F (N * X) = N * F X)
      hadd (by intro X; simp) fun j _ => ?_
    exact hsingle i j _
  set C := F 1 with hC
  have hFC : ∀ X, F X = X * C := fun X => by
    have := hall X 1
    rwa [Matrix.mul_one] at this
  have hr : ∀ i j (hij : i ≠ j), Matrix.single i j (1 : K) * C = C * Matrix.single i j 1 := by
    intro i j hij
    have h := hF 1 (transSL j i hij.symm 1) 1
    have e : ((transSL j i hij.symm 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ =
        1 + Matrix.single i j 1 := by
      rw [transSL_coe, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    rw [e, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.one_mul, hFC, ← hC] at h
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h
    exact add_left_cancel h
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_two (hr 0 1 (by decide)) (hr 1 0 (by decide))
  exact ⟨c, fun X => by rw [hFC, hc, Matrix.mul_smul, Matrix.mul_one]⟩

end Commutant

section End

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {K : Type} [Field K] [Algebra (ZMod 2) K]

theorem endIsField_of_tensor [Finite K] (h4 : 4 ≤ Nat.card K)
    {H : Subgroup (GLV V)} (φ : ↥H ≃* SL(2, K) × SL(2, K))
    (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
      ((φ γ).1 : Matrix (Fin 2) (Fin 2) K) * ψ v * ((φ γ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ) :
    EndIsField H (Module.finrank (ZMod 2) K) := by
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨φ', hφ'⟩ := exists_mulEquiv_omega_of_tensor h4 φ ψ hψ
  have : Nontrivial V := ψ.toEquiv.nontrivial
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite (ZMod 2) K := Module.finite_iff_finite.mpr inferInstance
  have hpos : Module.finrank (ZMod 2) K ≠ 0 :=
    (Module.finrank_pos (R := ZMod 2) (M := K)).ne'
  have hcardK : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [Nat.card_zmod] at this
    exact this
  have : Fintype (GaloisField 2 (Module.finrank (ZMod 2) K)) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 (Module.finrank (ZMod 2) K)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardK, GaloisField.card 2 _ hpos]
  have hmemK : ∀ a : K, scalarHom (coordEquiv ψ) a ∈ endCommutant H :=
    scalarHom_mem_endCommutant (coordEquiv ψ) φ' hφ'
  let θ : K →ₐ[ZMod 2] ↥(endCommutant H) :=
    (scalarHom (coordEquiv ψ)).codRestrict (endCommutant H) hmemK
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact (RingHom.injective (scalarHom (coordEquiv ψ) : K →+* Module.End (ZMod 2) V))
      (congrArg Subtype.val hab)
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨F, hF⟩ : ∃ F : Module.End (ZMod 2) (Matrix (Fin 2) (Fin 2) K),
        ∀ X, F X = ψ ((x : Module.End (ZMod 2) V) (ψ.symm X)) :=
      ⟨ψ.toLinearMap ∘ₗ (x : Module.End (ZMod 2) V) ∘ₗ ψ.symm.toLinearMap, fun X => rfl⟩
    have hFc : ∀ g h : SL(2, K), ∀ X : Matrix (Fin 2) (Fin 2) K,
        F ((g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) =
          (g : Matrix (Fin 2) (Fin 2) K) * F X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ := by
      intro g h X
      set γ : ↥H := φ.symm (g, h) with hγ
      have hφγ : φ γ = (g, h) := by simp [hγ]
      have hact : ∀ v, ψ ((γ : GLV V) v) =
          (g : Matrix (Fin 2) (Fin 2) K) * ψ v * (h : Matrix (Fin 2) (Fin 2) K)ᵀ := by
        intro v
        rw [hψ, hφγ]
      have key : ψ.symm ((g : Matrix (Fin 2) (Fin 2) K) * X *
          (h : Matrix (Fin 2) (Fin 2) K)ᵀ) = (γ : GLV V) (ψ.symm X) := by
        apply ψ.injective
        rw [hact, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      have hcomm := apply_of_mem_endCommutant x.2 γ.2 (ψ.symm X)
      rw [hF, hF, key, ← hcomm, hact]
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_tensor F hFc
    refine ⟨c, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    have h2 : ψ ((x : Module.End (ZMod 2) V) v) = c • ψ v := by
      have := hc (ψ v)
      rw [hF, LinearEquiv.symm_apply_apply] at this
      exact this
    show scalarHom (coordEquiv ψ) c v = (x : Module.End (ZMod 2) V) v
    rw [scalarHom_apply, coordEquiv_apply, coordEquiv_symm_apply, ← map_smul,
      LinearEquiv.apply_symm_apply, ← h2, LinearEquiv.symm_apply_apply]
  let E1 : K ≃ₐ[ZMod 2] ↥(endCommutant H) := AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  let E2 : K ≃ₐ[ZMod 2] GaloisField 2 (Module.finrank (ZMod 2) K) :=
    FiniteField.algEquivOfCardEq 2 hcard
  exact ⟨E1.symm.trans E2⟩

end End

section SelfDualSec

variable {K : Type} [Field K]

@[expose] def detPolar (X Y : Matrix (Fin 2) (Fin 2) K) : K :=
  X 0 0 * Y 1 1 - X 0 1 * Y 1 0 - X 1 0 * Y 0 1 + X 1 1 * Y 0 0

theorem detPolar_comm (X Y : Matrix (Fin 2) (Fin 2) K) : detPolar X Y = detPolar Y X := by
  simp only [detPolar]
  ring

theorem detPolar_add_left (X X' Y : Matrix (Fin 2) (Fin 2) K) :
    detPolar (X + X') Y = detPolar X Y + detPolar X' Y := by
  simp only [detPolar, Matrix.add_apply]
  ring

theorem detPolar_add_right (X Y Y' : Matrix (Fin 2) (Fin 2) K) :
    detPolar X (Y + Y') = detPolar X Y + detPolar X Y' := by
  simp only [detPolar, Matrix.add_apply]
  ring

theorem detPolar_zero_left (Y : Matrix (Fin 2) (Fin 2) K) : detPolar 0 Y = 0 := by
  simp [detPolar]

theorem detPolar_smul_right (X Y : Matrix (Fin 2) (Fin 2) K) (k : K) :
    detPolar X (k • Y) = k * detPolar X Y := by
  simp only [detPolar, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_zero_of_detPolar_eq_zero {X : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ Y, detPolar X Y = 0) : X = 0 := by
  have h1 := h (Matrix.single 1 1 1)
  have h2 := h (Matrix.single 1 0 1)
  have h3 := h (Matrix.single 0 1 1)
  have h4 := h (Matrix.single 0 0 1)
  simp [detPolar] at h1 h2 h3 h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [*]

theorem detPolar_tensor (g h X Y : Matrix (Fin 2) (Fin 2) K) :
    detPolar (g * X * hᵀ) (g * Y * hᵀ) = g.det * h.det * detPolar X Y := by
  simp only [detPolar, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]
  ring

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Algebra (ZMod 2) K]

@[expose] noncomputable def detTraceForm (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) :
    LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) K (detPolar (ψ x) (ψ y)))
    (fun x x' y => by
      rw [map_add, detPolar_add_left, map_add])
    (fun c x y => by
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc c with rfl | rfl
      · simp [detPolar_zero_left]
      · simp)
    (fun x y y' => by
      rw [map_add, detPolar_add_right, map_add])
    (fun c x y => by
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc c with rfl | rfl
      · simp [detPolar_comm _ 0, detPolar_zero_left]
      · simp)

theorem detTraceForm_apply (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) (x y : V) :
    detTraceForm ψ x y = Algebra.trace (ZMod 2) K (detPolar (ψ x) (ψ y)) := rfl

theorem detTraceForm_comm (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) (x y : V) :
    detTraceForm ψ x y = detTraceForm ψ y x := by
  rw [detTraceForm_apply, detTraceForm_apply, detPolar_comm]

theorem detTraceForm_separatingLeft [Finite K] (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K) :
    (detTraceForm ψ).SeparatingLeft := by
  intro x hx
  have hw : ∀ w : Matrix (Fin 2) (Fin 2) K, detPolar (ψ x) w = 0 := by
    intro w
    refine (traceForm_nondegenerate (ZMod 2) K).1 _ fun k => ?_
    rw [Algebra.traceForm_apply]
    have := hx (ψ.symm (k • w))
    rw [detTraceForm_apply, LinearEquiv.apply_symm_apply, detPolar_smul_right] at this
    rw [mul_comm]
    exact this
  exact ψ.injective (by simpa using eq_zero_of_detPolar_eq_zero hw)

theorem selfDual_of_tensor [Finite K] {L : Subgroup (GLV V)}
    (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (hL : ∀ (l : ↥L), ∃ g h : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ h.det = 1 ∧
      ∀ v, ψ ((l : GLV V) v) = g * ψ v * hᵀ) :
    SelfDual L ⊤ := by
  let f := (detTraceForm ψ).compl₁₂ (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap
    (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap
  have hf : ∀ i j : (⊤ : Submodule (ZMod 2) V), f i j = detTraceForm ψ i j := fun i j => rfl
  refine ⟨f, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  · have := detTraceForm_separatingLeft ψ (x : V) fun y => hx ⟨y, trivial⟩
    exact Subtype.ext this
  · have := detTraceForm_separatingLeft ψ (y : V) fun x => by
      rw [detTraceForm_comm]
      exact hy ⟨x, trivial⟩
    exact Subtype.ext this
  · intro k hk i j i' j' hi hj
    rw [hf, hf]
    have hi' : (i' : V) = (k : GLV V) i := hi.symm
    have hj' : (j' : V) = (k : GLV V) j := hj.symm
    rw [hi', hj', detTraceForm_apply, detTraceForm_apply]
    obtain ⟨g, h, hg, hh, hact⟩ := hL ⟨k, hk⟩
    simp only at hact
    rw [hact, hact, detPolar_tensor, hg, hh, one_mul, one_mul]

end SelfDualSec

theorem isNaturalMatrixModule_of_isTensorModel_two {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {n : ℕ} (hn : 2 ≤ n) {H : Subgroup (GLV V)}
    (hH : IsTensorModel 2 (GaloisField 2 n) H) :
    IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 (GaloisField 2 n))) ∧
      EndIsField H n ∧ SelfDual H ⊤ := by
  obtain ⟨φ₀, ψ, hψ₀⟩ := hH
  set K := GaloisField 2 n
  have hn0 : n ≠ 0 := by omega
  have h4 : 4 ≤ Nat.card K := by
    have : Nat.card K = 2 ^ n := by
      rw [GaloisField.card 2 n hn0]
    rw [this]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set σ := specialLinearGroupEquivStatedSL 2 K
  have hcoe : ∀ x : ↥(StatedSL 2 K), ((σ.symm x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := fun x => by
    have := specialLinearGroupEquivStatedSL_coe 2 K (σ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  let φ : ↥H ≃* SL(2, K) × SL(2, K) := φ₀.trans (MulEquiv.prodCongr σ.symm σ.symm)
  have hψ : ∀ (γ : ↥H) (v : V), ψ ((γ : GLV V) v) =
      ((φ γ).1 : Matrix (Fin 2) (Fin 2) K) * ψ v * ((φ γ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro γ v
    rw [hψ₀]
    show _ = ((σ.symm (φ₀ γ).1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ψ v *
      ((σ.symm (φ₀ γ).2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ
    rw [hcoe, hcoe]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨φ', hφ'⟩ := exists_mulEquiv_omega_of_tensor h4 φ ψ hψ
    exact ⟨φ', coordEquiv ψ, hφ'⟩
  · have := endIsField_of_tensor h4 φ ψ hψ
    rwa [GaloisField.finrank 2 hn0] at this
  · refine selfDual_of_tensor ψ fun l => ?_
    refine ⟨((φ l).1 : Matrix (Fin 2) (Fin 2) K), ((φ l).2 : Matrix (Fin 2) (Fin 2) K),
      (φ l).1.2, (φ l).2.2, fun v => hψ l v⟩

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
