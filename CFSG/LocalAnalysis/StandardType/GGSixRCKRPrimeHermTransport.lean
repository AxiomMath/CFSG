module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

private lemma rckRPht_vecMul_antidiag_eq_aform {K : Type*} [Field K] {m : ℕ}
    (σ : K ≃+* K) (x y : Fin m → K) :
    Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag m) ⬝ᵥ y =
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ x y := by
  rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform, Matrix.dotProduct_mulVec]

private lemma rckRPht_antidiag_map {F L : Type*} [Field F] [Field L]
    (τ : F ≃+* L) (m : ℕ) :
    (Unitary.antidiag m : Matrix (Fin m) (Fin m) F).map τ = Unitary.antidiag m := by
  ext i j
  by_cases h : j = Fin.rev i <;> simp [Unitary.antidiag, h]

private lemma rckRPht_conjTr_map {F L : Type*} [Field F] [Field L]
    {σF : F ≃+* F} {σL : L ≃+* L} (τ : F ≃+* L)
    (hτ : ∀ c, τ (σF c) = σL (τ c)) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) :
    Unitary.conjTr σL (M.map τ) = (Unitary.conjTr σF M).map τ := by
  ext i j
  simp only [Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply]
  exact (hτ (M j i)).symm

private lemma rckRPht_conjTr_map_symm {F L : Type*} [Field F] [Field L]
    {σF : F ≃+* F} {σL : L ≃+* L} (τ : F ≃+* L)
    (hτ : ∀ c, τ (σF c) = σL (τ c)) {m : ℕ} (M : Matrix (Fin m) (Fin m) L) :
    Unitary.conjTr σF (M.map τ.symm) = (Unitary.conjTr σL M).map τ.symm := by
  ext i j
  simp only [Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply]
  have h := hτ (τ.symm (M j i))
  rw [τ.apply_symm_apply] at h
  simpa using congrArg τ.symm h

private lemma rckRPht_map_conjTr_mul {F L : Type*} [Field F] [Field L]
    {σF : F ≃+* F} {σL : L ≃+* L} (τ : F ≃+* L)
    (hτ : ∀ c, τ (σF c) = σL (τ c)) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) F)
    (hA : Unitary.conjTr σF A * Unitary.antidiag m * A = Unitary.antidiag m) :
    Unitary.conjTr σL (A.map τ) * Unitary.antidiag m * (A.map τ) =
      Unitary.antidiag m := by
  rw [rckRPht_conjTr_map τ hτ, ← rckRPht_antidiag_map τ m,
    ← Matrix.map_mul, ← Matrix.map_mul, hA, rckRPht_antidiag_map]

private lemma rckRPht_det_map {F L : Type*} [Field F] [Field L]
    (τ : F ≃+* L) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) :
    (M.map τ).det = τ M.det := by
  simpa [RingHom.mapMatrix_apply] using (RingHom.map_det τ.toRingHom M).symm

private lemma rckRPht_det_coords {K : Type*} [Field K] {m : ℕ}
    (A : GL (Fin m) K) :
    LinearMap.det ((LinearMap.GeneralLinearGroup.toLinearEquiv
      (Matrix.GeneralLinearGroup.toLin A) :
        (Fin m → K) ≃ₗ[K] (Fin m → K)) : (Fin m → K) →ₗ[K] (Fin m → K)) =
      (A : Matrix (Fin m) (Fin m) K).det := by
  change LinearMap.det (Matrix.toLin' (A : Matrix (Fin m) (Fin m) K)) =
    (A : Matrix (Fin m) (Fin m) K).det
  rw [LinearMap.det_toLin']

private lemma rckRPht_toLE_apply {K : Type*} [Field K] {m : ℕ}
    (A : GL (Fin m) K) (v : Fin m → K) :
    LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin A) v =
      (A : Matrix (Fin m) (Fin m) K) *ᵥ v := by
  rfl

private lemma rckRPht_det_conj_coords {K W : Type} [Field K] [AddCommGroup W]
    [Module K W] {m : ℕ} (e : W ≃ₗ[K] (Fin m → K))
    (L : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    LinearMap.det (((e.trans (L.trans e.symm)) : W ≃ₗ[K] W) : W →ₗ[K] W) =
      LinearMap.det (L : (Fin m → K) →ₗ[K] (Fin m → K)) := by
  have hmap : (L : (Fin m → K) →ₗ[K] (Fin m → K)) =
      (e : W →ₗ[K] (Fin m → K)) ∘ₗ
        (((e.trans (L.trans e.symm)) : W ≃ₗ[K] W) : W →ₗ[K] W) ∘ₗ
          (e.symm : (Fin m → K) →ₗ[K] W) := by
    ext v
    simp [LinearEquiv.trans_apply]
  rw [hmap, LinearMap.det_conj]

private lemma rckRPht_conj_apply {K W : Type} [Field K] [AddCommGroup W]
    [Module K W] {m : ℕ} (e : W ≃ₗ[K] (Fin m → K))
    (L : (Fin m → K) ≃ₗ[K] (Fin m → K)) (w : W) :
    e ((e.trans (L.trans e.symm)) w) = L (e w) := by
  simp [LinearEquiv.trans_apply]

private lemma rckRPht_det_toMatrix_conj {K W : Type} [Field K] [AddCommGroup W]
    [Module K W] {m : ℕ} (e : W ≃ₗ[K] (Fin m → K)) (g : W ≃ₗ[K] W) :
    (LinearMap.toMatrix' ((e : W →ₗ[K] (Fin m → K)) ∘ₗ
      (g : W →ₗ[K] W) ∘ₗ (e.symm : (Fin m → K) →ₗ[K] W))).det =
      LinearMap.det (g : W →ₗ[K] W) := by
  rw [LinearMap.det_toMatrix', LinearMap.det_conj]

private lemma rckRPht_one_le_of_card {F : Type*} [Field F] [Finite F] {f : ℕ}
    (h : Nat.card F = (2 ^ f) ^ 2) : 1 ≤ f := by
  classical
  letI := Fintype.ofFinite F
  have h2 : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf
    have h1 : Nat.card F = 1 := by simpa using h
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  · omega

private lemma rckRPht_unitaryFieldData {F : Type*} [Field F] {f : ℕ}
    (h : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) : UnitaryFieldData 2 f F where
  prime := Nat.prime_two
  one_le := hf
  card := by
    rw [h, ← pow_mul, Nat.mul_comm f 2]

private lemma rckRPht_exists_tau {F₀ K : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
    [Field K] [Finite K] {f : ℕ} (hc : Nat.card F₀ = (2 ^ f) ^ 2)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ τ : F₀ ≃+* K,
      ∀ c, τ (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f c) = σ (τ c) := by
  classical
  letI := Fintype.ofFinite F₀
  letI := Fintype.ofFinite K
  have hf : 1 ≤ f := rckRPht_one_le_of_card hc
  let hF₀U : UnitaryFieldData 2 f F₀ := rckRPht_unitaryFieldData hc hf
  let hKU : UnitaryFieldData 2 f K := rckRPht_unitaryFieldData hK hf
  haveI : CharP F₀ 2 := hF₀U.charP
  haveI : CharP K 2 := hKU.charP
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f :=
    AutPSU.eq_sigma_of_mul_self_eq_one hKU (by simpa [pow_two] using hσ2) hσ1
  let σ₀ : F₀ ≃+* F₀ := CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f
  have hσ₀2 : σ₀ * σ₀ = 1 := by
    ext c
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hc c
  have hσ₀1 : σ₀ ≠ 1 := by
    obtain ⟨c, hcne⟩ := hF₀U.exists_bar_ne
    intro h1
    apply hcne
    rw [RootDetectSU.bar_eq hF₀U]
    exact congrArg (fun e : F₀ ≃+* F₀ => e c) h1
  have hcard : Fintype.card F₀ = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc, hK]
  let τ : F₀ ≃+* K := FiniteField.ringEquivOfCardEq hcard
  set ψ : K ≃+* K := τ.symm.trans (σ₀.trans τ) with hψdef
  have hψ2 : ψ * ψ = 1 := by
    ext c
    change τ (σ₀ (τ.symm (τ (σ₀ (τ.symm c))))) = c
    rw [τ.symm_apply_apply, CFSG.LieType.BorelTits.unitaryInvolution_involutive hc,
      τ.apply_symm_apply]
  have hψ1 : ψ ≠ 1 := by
    intro hψ
    apply hσ₀1
    ext c
    have h := congrArg (fun e : K ≃+* K => e (τ c)) hψ
    change τ (σ₀ (τ.symm (τ c))) = τ c at h
    rw [τ.symm_apply_apply] at h
    exact τ.injective h
  have hψeq : ψ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f :=
    AutPSU.eq_sigma_of_mul_self_eq_one hKU hψ2 hψ1
  have hψσ : ψ = σ := hψeq.trans hσeq.symm
  refine ⟨τ, fun c => ?_⟩
  have h := congrArg (fun e : K ≃+* K => e (τ c)) hψσ
  change τ (σ₀ (τ.symm (τ c))) = σ (τ c) at h
  simpa only [τ.symm_apply_apply] using h

theorem exists_suModel_of_hermForm_explicit {F₀ K W : Type} [Field F₀] [Finite F₀] [CharP F₀ 2]
    [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] {f m : ℕ}
    (hc : Nat.card F₀ = (2 ^ f) ^ 2) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hW : Module.finrank K W = m) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (hβs : β.IsSymm) (hβn : β.SeparatingLeft) :
    ∃ (τ : F₀ ≃+* K) (e : W ≃ₗ[K] (Fin m → K))
      (ρ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f) m) →* (W ≃ₗ[K] W)),
      (∀ c, τ (CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f c) = σ (τ c)) ∧
      (∀ x y, Matrix.vecMul (fun i => σ (e x i)) (Unitary.antidiag m) ⬝ᵥ e y = β x y) ∧
      (∀ A w, e (ρ A w) =
        (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w) ∧
      Function.Injective ρ ∧
      ∀ g : W ≃ₗ[K] W, g ∈ ρ.range ↔
        (∀ w w', β (g w) (g w') = β w w') ∧ LinearMap.det (g : W →ₗ[K] W) = 1 := by
  classical
  subst hW
  let m := Module.finrank K W
  have hf : 1 ≤ f := rckRPht_one_le_of_card hc
  have hKU : UnitaryFieldData 2 f K := rckRPht_unitaryFieldData hK hf
  letI : CharP K 2 := hKU.charP
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f :=
    AutPSU.eq_sigma_of_mul_self_eq_one hKU (by simpa [pow_two] using hσ2) hσ1
  obtain ⟨τ, hτ⟩ := rckRPht_exists_tau hc hK hσ2 hσ1
  let σ₀ : F₀ ≃+* F₀ := CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 f
  have hβnd : β.Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBUnitaryB.nondegenerate_of_isSymm hβs hβn
  obtain ⟨e₁, he₁⟩ :=
    CFSG.ComponentClassification.CatalogueBHermitian.exists_coordinate_isometry
      (sigma := σ) β hβs hβnd hσ2 hσ1
  let e₁' : W ≃ₗ[K] (Fin m → K) := e₁
  have he₁' : ∀ x y,
      CFSG.ClassicalGroups.Unitary.herm σ (e₁' x) (e₁' y) = β x y := he₁
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix (F := K) (p := 2) (f := f) hK m
  have hPσ : Unitary.conjTr σ (P : Matrix (Fin m) (Fin m) K) *
      (P : Matrix (Fin m) (Fin m) K) = Unitary.antidiag m := by
    simpa [hσeq] using hP
  let Amat : Matrix (Fin m) (Fin m) K :=
    ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  have hPA : (P : Matrix (Fin m) (Fin m) K) * Amat = 1 := by
    change (P : Matrix (Fin m) (Fin m) K) *
      (((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAP : Amat * (P : Matrix (Fin m) (Fin m) K) = 1 := by
    change (((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
      (P : Matrix (Fin m) (Fin m) K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconjPA : Unitary.conjTr σ Amat * Unitary.conjTr σ (P : Matrix _ _ K) = 1 := by
    rw [← Unitary.conjTr_mul, hPA, Unitary.conjTr_one]
  have hAiso : Unitary.conjTr σ Amat * Unitary.antidiag m * Amat = 1 := by
    calc Unitary.conjTr σ Amat * Unitary.antidiag m * Amat
        = Unitary.conjTr σ Amat *
            (Unitary.conjTr σ (P : Matrix _ _ K) * (P : Matrix _ _ K)) * Amat := by
          rw [hPσ]
      _ = (Unitary.conjTr σ Amat * Unitary.conjTr σ (P : Matrix _ _ K)) *
            ((P : Matrix _ _ K) * Amat) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hconjPA, hPA, Matrix.one_mul]
  let toLE : LinearMap.GeneralLinearGroup K (Fin m → K) →*
      ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
    { toFun := LinearMap.GeneralLinearGroup.toLinearEquiv
      map_one' := by
        ext v
        rfl
      map_mul' := LinearMap.GeneralLinearGroup.toLinearEquiv_mul }
  let coords : GL (Fin m) K →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
    toLE.comp Matrix.GeneralLinearGroup.toLin.toMonoidHom
  let eMat : (Fin m → K) ≃ₗ[K] (Fin m → K) := coords P⁻¹
  let e : W ≃ₗ[K] (Fin m → K) := e₁'.trans eMat
  have he_apply : ∀ x, e x = Amat *ᵥ e₁' x := by
    intro x
    exact rckRPht_toLE_apply (P⁻¹) (e₁' x)
  have he_gram : ∀ x y,
      Matrix.vecMul (fun i => σ (e x i)) (Unitary.antidiag m) ⬝ᵥ e y = β x y := by
    intro x y
    rw [rckRPht_vecMul_antidiag_eq_aform]
    rw [he_apply x, he_apply y]
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_mulVec]
    rw [hAiso, Matrix.one_mulVec]
    simpa [CFSG.ClassicalGroups.Unitary.herm_def, dotProduct] using he₁' x y
  let conj : ((Fin m → K) ≃ₗ[K] (Fin m → K)) →* (W ≃ₗ[K] W) :=
    { toFun := fun L => e.trans (L.trans e.symm)
      map_one' := by
        ext w
        simp [LinearEquiv.trans_apply]
      map_mul' := by
        intro L L'
        ext w
        simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply] }
  let ρ : ↥(Unitary.SU σ₀ m) →* (W ≃ₗ[K] W) :=
    conj.comp (coords.comp
      ((Matrix.GeneralLinearGroup.map τ.toRingHom).comp (Subgroup.subtype _)))
  have hρ_apply : ∀ A w, e (ρ A w) =
      (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w := by
    intro A w
    change e ((e.trans
      ((coords (Matrix.GeneralLinearGroup.map τ.toRingHom (A : GL (Fin m) F₀))).trans
        e.symm)) w) = _
    rw [rckRPht_conj_apply]
    change (LinearMap.GeneralLinearGroup.toLinearEquiv
      (Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map τ.toRingHom (A : GL (Fin m) F₀)))) (e w) = _
    rw [rckRPht_toLE_apply, Matrix.GeneralLinearGroup.val_map_apply]
    rfl
  have hρ_inj : Function.Injective ρ := by
    intro A B hAB
    apply Subtype.ext
    apply Units.ext
    have hfun : ∀ w,
        (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w =
          (((B : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w := by
      intro w
      rw [← hρ_apply A w, hAB, hρ_apply B w]
    have hvec : ∀ v : Fin m → K,
        (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ v =
          (((B : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ v := by
      intro v
      obtain ⟨w, rfl⟩ := e.surjective v
      exact hfun w
    have hmat : (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) =
        (((B : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) := by
      ext i j
      have h := congrFun (hvec (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact Matrix.map_injective τ.injective hmat
  have hdet_forward : ∀ A : ↥(Unitary.SU σ₀ m),
      LinearMap.det ((ρ A : W ≃ₗ[K] W) : W →ₗ[K] W) = 1 := by
    intro A
    let L : (Fin m → K) ≃ₗ[K] (Fin m → K) :=
      coords (Matrix.GeneralLinearGroup.map τ.toRingHom (A : GL (Fin m) F₀))
    have hρA : (ρ A : W ≃ₗ[K] W) = e.trans (L.trans e.symm) := rfl
    rw [hρA, rckRPht_det_conj_coords e L]
    change LinearMap.det ((LinearMap.GeneralLinearGroup.toLinearEquiv
      (Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map τ.toRingHom (A : GL (Fin m) F₀)))) :
          (Fin m → K) →ₗ[K] (Fin m → K)) = 1
    rw [rckRPht_det_coords]
    rw [show ((Matrix.GeneralLinearGroup.map τ.toRingHom (A : GL (Fin m) F₀)) :
        Matrix (Fin m) (Fin m) K) =
      (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) from rfl]
    rw [rckRPht_det_map, (Unitary.mem_SU.mp A.2).1, map_one]
  have hβaform : ∀ x y, β x y =
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ (e x) (e y) := by
    intro x y
    exact (he_gram x y).symm.trans (rckRPht_vecMul_antidiag_eq_aform σ (e x) (e y))
  have hiso_forward : ∀ A : ↥(Unitary.SU σ₀ m),
      ∀ w w', β (ρ A w) (ρ A w') = β w w' := by
    intro A w w'
    have hM : Unitary.conjTr σ
        (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *
          Unitary.antidiag m *
            (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) =
        Unitary.antidiag m :=
      rckRPht_map_conjTr_mul τ hτ _ (Unitary.mem_SU.mp A.2).2
    calc β (ρ A w) (ρ A w')
        = CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ
            (e (ρ A w)) (e (ρ A w')) := hβaform _ _
      _ = CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ
            ((((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w)
            ((((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *ᵥ e w') := by
          rw [hρ_apply, hρ_apply]
      _ = (fun i => σ (e w i)) ⬝ᵥ
            ((Unitary.conjTr σ
              (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) *
                Unitary.antidiag m *
                  (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ)) *ᵥ e w') :=
          CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_mulVec σ _ _ _
      _ = CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ (e w) (e w') := by
          rw [hM]
          rfl
      _ = β w w' := (hβaform w w').symm
  refine ⟨τ, e, ρ, hτ, he_gram, hρ_apply, hρ_inj, ?_⟩
  intro g
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨hiso_forward A, hdet_forward A⟩
  · rintro ⟨hg_iso, hg_det⟩
    let fₗ : (Fin m → K) →ₗ[K] (Fin m → K) :=
      (e : W →ₗ[K] (Fin m → K)) ∘ₗ (g : W →ₗ[K] W) ∘ₗ
        (e.symm : (Fin m → K) →ₗ[K] W)
    let M : Matrix (Fin m) (Fin m) K := LinearMap.toMatrix' fₗ
    have hMlin : Matrix.toLin' M = fₗ := by
      change Matrix.toLin' (LinearMap.toMatrix' fₗ) = fₗ
      simpa [Matrix.toLin'_symm] using
        (LinearEquiv.apply_symm_apply (Matrix.toLin' (R := K)
          (n := Fin m) (m := Fin m)) fₗ)
    have hMx : ∀ x : Fin m → K, M *ᵥ x = e (g (e.symm x)) := by
      intro x
      have h := DFunLike.congr_fun hMlin x
      simpa [fₗ, Matrix.toLin'_apply', Matrix.mulVecLin_apply] using h
    have hMdet : M.det = 1 := by
      rw [rckRPht_det_toMatrix_conj e g]
      exact hg_det
    have hMiso : Unitary.conjTr σ M * Unitary.antidiag m * M = Unitary.antidiag m := by
      refine (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_isometry_iff σ M).mp ?_
      intro x y
      rw [hMx x, hMx y]
      calc CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ
            (e (g (e.symm x))) (e (g (e.symm y)))
          = β (g (e.symm x)) (g (e.symm y)) := (hβaform _ _).symm
        _ = β (e.symm x) (e.symm y) := hg_iso _ _
        _ = CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ
              (e (e.symm x)) (e (e.symm y)) := hβaform _ _
        _ = CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform σ x y := by
            rw [e.apply_symm_apply, e.apply_symm_apply]
    have hMdet' : (M.map τ.symm).det ≠ 0 := by
      rw [rckRPht_det_map, hMdet, map_one]
      exact one_ne_zero
    let A : GL (Fin m) F₀ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map τ.symm) hMdet'
    have hAval : (A : Matrix (Fin m) (Fin m) F₀) = M.map τ.symm := rfl
    have hAconj : Unitary.conjTr σ₀ (M.map τ.symm) * Unitary.antidiag m *
        (M.map τ.symm) = Unitary.antidiag m := by
      have h := congrArg (fun X : Matrix (Fin m) (Fin m) K => X.map τ.symm) hMiso
      rw [Matrix.map_mul, Matrix.map_mul, ← rckRPht_conjTr_map_symm τ hτ,
        rckRPht_antidiag_map τ.symm m] at h
      exact h
    have hA_mem : A ∈ Unitary.SU σ₀ m := by
      rw [Unitary.mem_SU]
      exact ⟨by rw [hAval, rckRPht_det_map, hMdet, map_one],
        by rw [hAval]; exact hAconj⟩
    refine ⟨⟨A, hA_mem⟩, ?_⟩
    apply LinearEquiv.ext
    intro w
    apply e.injective
    rw [hρ_apply]
    have hmapτ : (((A : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀).map τ) = M := by
      rw [hAval]
      ext i j
      simp
    rw [hmapτ]
    rw [hMx]
    simp

end CFSG.StandardType.RCKRP
