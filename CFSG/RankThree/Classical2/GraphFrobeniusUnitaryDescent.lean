module

public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.RankThree.Classical2

open Matrix CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

section InvTranspose

variable {R : Type*} [CommRing R] {n : ℕ}

@[expose] def invTransposeHom : GL (Fin n) R →* GL (Fin n) R where
  toFun X := ⟨(↑X⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ, (X : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← Matrix.transpose_mul, X.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, X.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' X Y := Units.ext (by
    change (↑(X * Y)⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ = (↑X⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ *
      (↑Y⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem coe_invTransposeHom (X : GL (Fin n) R) :
    (invTransposeHom X : Matrix (Fin n) (Fin n) R) = (↑X⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ :=
  rfl

theorem coe_invTransposeHom_inv (X : GL (Fin n) R) :
    (↑(invTransposeHom X)⁻¹ : Matrix (Fin n) (Fin n) R) = (X : Matrix (Fin n) (Fin n) R)ᵀ :=
  rfl

theorem invTransposeHom_invTransposeHom (X : GL (Fin n) R) :
    invTransposeHom (invTransposeHom X) = X :=
  Units.ext (by rw [coe_invTransposeHom, coe_invTransposeHom_inv, Matrix.transpose_transpose])

theorem map_invTransposeHom {S : Type*} [CommRing S] (φ : R →+* S) (X : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map φ (invTransposeHom X) =
      invTransposeHom (Matrix.GeneralLinearGroup.map φ X) := by
  refine Units.ext ?_
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_invTransposeHom, coe_invTransposeHom, ← map_inv,
    Matrix.transpose_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply]

theorem coe_generalLinearGroup_map {S : Type*} [CommRing S] (φ : R →+* S) (X : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.map φ X : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) =
      (X : Matrix (Fin n) (Fin n) R).map φ := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]

end InvTranspose

section Hermitian

variable {F : Type*} [Field F] {n : ℕ}

theorem conjTr_nonsing_inv (σ : F ≃+* F) {M : Matrix (Fin n) (Fin n) F} (hM : IsUnit M.det) :
    CFSG.LieType.Universal.Unitary.conjTr σ M⁻¹ =
      (CFSG.LieType.Universal.Unitary.conjTr σ M)⁻¹ := by
  have hmap : (M.map σ)⁻¹ = M⁻¹.map σ := by
    apply Matrix.inv_eq_left_inv
    change σ.toRingHom.mapMatrix M⁻¹ * σ.toRingHom.mapMatrix M = 1
    rw [← map_mul, Matrix.nonsing_inv_mul M hM, map_one]
  rw [CFSG.LieType.Universal.Unitary.conjTr, CFSG.LieType.Universal.Unitary.conjTr, ← hmap,
    Matrix.transpose_nonsing_inv]

end Hermitian

section Descent

variable {ℓ f : ℕ} {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {n : ℕ}

theorem matrix_graph_frobenius_unitary_descent (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) [IsAlgClosure K Ω] (hn : 1 ≤ n) (A : GL (Fin n) Ω) :
    let q := ℓ ^ f
    let τ : Matrix (Fin n) (Fin n) Ω → Matrix (Fin n) (Fin n) Ω := fun X => ((X.map (· ^ q))⁻¹)ᵀ
    ∃ H : GL (Fin n) Ω, (H : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
      (∀ X : GL (Fin n) Ω, (X : Matrix (Fin n) (Fin n) Ω).det = 1 →
        (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) * ((A : Matrix (Fin n) (Fin n) Ω) *
          τ ((H : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω) *
            (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω)) * (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω)) *
          (H : Matrix (Fin n) (Fin n) Ω) = τ (X : Matrix (Fin n) (Fin n) Ω)) ∧
      {X : GL (Fin n) Ω | (X : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
          (A : Matrix (Fin n) (Fin n) Ω) * τ (X : Matrix (Fin n) (Fin n) Ω) *
            (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) = X} =
        (fun Y => H * Y * H⁻¹) '' unitarySet (Ω := Ω) q n := by
  intro q τ
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  let φ : Ω →+* Ω := iterateFrobenius Ω ℓ f
  have hφ : ∀ c, φ c = c ^ q := fun c => iterateFrobenius_def ℓ f c
  let σG : GL (Fin n) Ω →* GL (Fin n) Ω := Matrix.GeneralLinearGroup.map φ
  let τG : GL (Fin n) Ω →* GL (Fin n) Ω := invTransposeHom.comp σG
  have hσG : ∀ X : GL (Fin n) Ω,
      (σG X : Matrix (Fin n) (Fin n) Ω) = (X : Matrix (Fin n) (Fin n) Ω).map (· ^ q) := by
    intro X
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hφ, Matrix.map_apply]
  have hτ : ∀ X : GL (Fin n) Ω, τ (X : Matrix (Fin n) (Fin n) Ω) = (τG X : Matrix _ _ Ω) := by
    intro X
    change (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ q))⁻¹)ᵀ = (↑(σG X)⁻¹ : Matrix _ _ Ω)ᵀ
    rw [← hσG, Matrix.coe_units_inv]
  have hττ : ∀ X, τG (τG X) = σG (σG X) := by
    intro X
    change invTransposeHom (σG (invTransposeHom (σG X))) = σG (σG X)
    rw [map_invTransposeHom, invTransposeHom_invTransposeHom]
  have hKpow : ∀ x : K, x ^ q = x := fun x => by
    rw [show q = Fintype.card K by rw [← Nat.card_eq_fintype_card, hK]]
    exact FiniteField.pow_card x
  let K₂ : IntermediateField K Ω := Subfield.toIntermediateField
    (RingHom.eqLocusField (iterateFrobenius Ω ℓ (2 * f)) (RingHom.id Ω)) (fun x => by
      rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, ← map_pow,
        pow_mul', pow_pow_eq_self (hKpow x) 2])
  have hmemK₂ : ∀ c : Ω, c ∈ K₂ ↔ c ^ q ^ 2 = c := fun c => by
    change c ∈ RingHom.eqLocusField _ _ ↔ _
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, pow_mul']
  have hcard₂ : Nat.card K₂ = ℓ ^ (2 * f) := by
    rw [← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [hmemK₂]
    change c ^ (ℓ ^ f) ^ 2 = c ↔ c ^ ℓ ^ (2 * f) = c
    rw [pow_mul']
  have : CharP K₂ ℓ := charP_of_injective_algebraMap (algebraMap K K₂).injective ℓ
  have : IsAlgClosure K₂ Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
  set N : GL (Fin n) Ω := A * τG A with hNdef
  obtain ⟨⟨H', hH'⟩, -⟩ := matrix_frobenius_lang (K := K₂) (Ω := Ω) hℓ (by omega) hcard₂ hn N
  have hσσ : ∀ X : GL (Fin n) Ω, (σG (σG X) : Matrix (Fin n) (Fin n) Ω) =
      (X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ (2 * f)) := by
    intro X
    rw [hσG, hσG, Matrix.map_map]
    congr 1
    funext c
    change (c ^ q) ^ q = c ^ ℓ ^ (2 * f)
    rw [← pow_mul, ← sq, ← pow_mul, mul_comm]
  have hN : N = H'⁻¹ * σG (σG H') := Units.ext (by rw [hH', Units.val_mul, hσσ])
  set C : GL (Fin n) Ω := H'⁻¹ with hCdef
  have hNC : N = C * (σG (σG C))⁻¹ := by
    rw [hN, hCdef, map_inv, map_inv, inv_inv]
  set A₁ : GL (Fin n) Ω := C⁻¹ * A * τG C with hA₁def
  have hA₁τ : A₁ * τG A₁ = 1 := by
    have h1 : A * τG A = C * (σG (σG C))⁻¹ := hNC
    simp only [hA₁def, map_mul, map_inv, hττ]
    calc C⁻¹ * A * τG C * ((τG C)⁻¹ * τG A * σG (σG C)) =
        C⁻¹ * (A * τG A) * σG (σG C) := by group
      _ = 1 := by rw [h1]; group
  have hherm : ((A₁ : Matrix (Fin n) (Fin n) Ω).map φ)ᵀ = A₁ := by
    have h1 : τG A₁ = A₁⁻¹ := eq_inv_of_mul_eq_one_right hA₁τ
    have h2 : σG A₁ = invTransposeHom A₁⁻¹ := by
      rw [← h1]
      exact (invTransposeHom_invTransposeHom _).symm
    have h3 := congrArg (fun X : GL (Fin n) Ω => (X : Matrix (Fin n) (Fin n) Ω)) h2
    simp only [coe_invTransposeHom, inv_inv] at h3
    change (((σG A₁ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω))ᵀ = _
    rw [h3, Matrix.transpose_transpose]
  have hσσA₁ : ((A₁ : Matrix (Fin n) (Fin n) Ω).map φ).map φ = A₁ := by
    have h1 : (A₁ : Matrix (Fin n) (Fin n) Ω).map φ = (A₁ : Matrix (Fin n) (Fin n) Ω)ᵀ := by
      have h := congrArg Matrix.transpose hherm
      rwa [Matrix.transpose_transpose] at h
    rw [h1, Matrix.transpose_map, h1, Matrix.transpose_transpose]
  have hA₁mem : ∀ i j, (A₁ : Matrix (Fin n) (Fin n) Ω) i j ∈ K₂ := by
    intro i j
    rw [hmemK₂]
    have := congrFun (congrFun hσσA₁ i) j
    simp only [Matrix.map_apply, hφ] at this
    rw [pow_two, pow_mul]
    exact this
  let ι : K₂ →+* Ω := algebraMap K₂ Ω
  let A₁' : Matrix (Fin n) (Fin n) K₂ := fun i j => ⟨A₁ i j, hA₁mem i j⟩
  have hA₁'map : A₁'.map ι = A₁ := rfl
  have hK2 : UnitaryFieldData ℓ f K₂ := ⟨hℓ, hf, hcard₂⟩
  let σ₂ : K₂ ≃+* K₂ :=
    { hK2.bar with
      invFun := hK2.bar
      left_inv := hK2.bar_bar
      right_inv := hK2.bar_bar }
  have hσ₂ : ∀ c : K₂, ι (σ₂ c) = φ (ι c) := fun c => by
    change ι (hK2.bar c) = φ (ι c)
    rw [hK2.bar_apply, map_pow, hφ]
  have hunit : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ₂ :=
    { invol := hK2.bar_bar
      exists_ne := hK2.exists_bar_ne
      trace_surj := fun a ha => by
        obtain ⟨c, hc⟩ := hK2.traceLin_surjective ⟨a, ha⟩
        exact ⟨c, congrArg Subtype.val hc⟩
      norm_surj := fun d hd _ => by
        obtain ⟨c, hc⟩ := hK2.normHom_surjective ⟨d, hd⟩
        exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩ }
  have hιinj : Function.Injective fun M : Matrix (Fin n) (Fin n) K₂ => M.map ι :=
    Matrix.map_injective ι.injective
  have hconjTrmap : ∀ M : Matrix (Fin n) (Fin n) K₂,
      (CFSG.LieType.Universal.Unitary.conjTr σ₂ M).map ι = ((M.map ι).map φ)ᵀ := by
    intro M
    ext i j
    simp only [CFSG.LieType.Universal.Unitary.conjTr, Matrix.map_apply, Matrix.transpose_apply]
    exact hσ₂ _
  have hherm' : CFSG.LieType.Universal.Unitary.conjTr σ₂ A₁' = A₁' := by
    apply hιinj
    change (CFSG.LieType.Universal.Unitary.conjTr σ₂ A₁').map ι = A₁'.map ι
    rw [hconjTrmap, hA₁'map]
    exact hherm
  have hA₁'det : IsUnit A₁'.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h := RingHom.map_det ι A₁'
    rw [h0, map_zero, RingHom.mapMatrix_apply, hA₁'map] at h
    exact (Matrix.GeneralLinearGroup.det_ne_zero A₁) h.symm
  have hGherm : CFSG.LieType.Universal.Unitary.conjTr σ₂ A₁'⁻¹ = A₁'⁻¹ := by
    rw [conjTr_nonsing_inv σ₂ hA₁'det, hherm']
  have hGdet : A₁'⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hA₁'det.ne_zero
  obtain ⟨P, hP⟩ :=
    CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hunit hGherm hGdet
  set X₀ := CFSG.LieType.Universal.Unitary.conjTr σ₂ (P : Matrix (Fin n) (Fin n) K₂) with hX₀
  have hPX : (P : Matrix (Fin n) (Fin n) K₂) * X₀ = A₁' := by
    have h1 : X₀ * A₁'⁻¹ = (↑P⁻¹ : Matrix (Fin n) (Fin n) K₂) := by
      calc X₀ * A₁'⁻¹ = X₀ * A₁'⁻¹ * ((P : Matrix (Fin n) (Fin n) K₂) *
            (↑P⁻¹ : Matrix (Fin n) (Fin n) K₂)) := by rw [P.mul_inv, Matrix.mul_one]
        _ = X₀ * A₁'⁻¹ * (P : Matrix (Fin n) (Fin n) K₂) *
            (↑P⁻¹ : Matrix (Fin n) (Fin n) K₂) := (Matrix.mul_assoc _ _ _).symm
        _ = (↑P⁻¹ : Matrix (Fin n) (Fin n) K₂) := by rw [hP, Matrix.one_mul]
    have h2 : (P : Matrix (Fin n) (Fin n) K₂) * X₀ * A₁'⁻¹ = 1 := by
      rw [Matrix.mul_assoc, h1, P.mul_inv]
    have h3 : A₁'⁻¹⁻¹ = (P : Matrix (Fin n) (Fin n) K₂) * X₀ := Matrix.inv_eq_left_inv h2
    rw [← h3, Matrix.nonsing_inv_nonsing_inv _ hA₁'det]
  set PΩ : GL (Fin n) Ω := Matrix.GeneralLinearGroup.map ι P with hPΩ
  have hA₁P : A₁ = PΩ * (τG PΩ)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul]
    change (A₁ : Matrix (Fin n) (Fin n) Ω) = (PΩ : Matrix (Fin n) (Fin n) Ω) *
      ((σG PΩ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω)ᵀ
    rw [← hA₁'map, ← hPX]
    change ι.mapMatrix ((P : Matrix (Fin n) (Fin n) K₂) * X₀) = _
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hX₀, hconjTrmap]
    change _ = ((Matrix.GeneralLinearGroup.map ι P : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) *
      ((Matrix.GeneralLinearGroup.map φ (Matrix.GeneralLinearGroup.map ι P) : GL (Fin n) Ω) :
        Matrix (Fin n) (Fin n) Ω)ᵀ
    rw [coe_generalLinearGroup_map, coe_generalLinearGroup_map, coe_generalLinearGroup_map]
  set H₀ : GL (Fin n) Ω := C * PΩ with hH₀def
  have hA : A = H₀ * (τG H₀)⁻¹ := by
    have h1 : A = C * A₁ * (τG C)⁻¹ := by rw [hA₁def]; group
    rw [h1, hA₁P, hH₀def, map_mul]
    group
  have hconj₀ : ∀ X, H₀⁻¹ * (A * τG (H₀ * X * H₀⁻¹) * A⁻¹) * H₀ = τG X := by
    intro X
    rw [hA]
    simp only [map_mul, map_inv]
    group
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((H₀ : Matrix (Fin n) (Fin n) Ω).det)⁻¹
    (by omega : 0 < n)
  have hH₀det : (H₀ : Matrix (Fin n) (Fin n) Ω).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero H₀
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact inv_ne_zero hH₀det hc.symm
  set s : GL (Fin n) Ω := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) with hsdef
  have hcent : ∀ g : GL (Fin n) Ω, s * g = g * s := fun g => Units.ext (by
    rw [Units.val_mul, Units.val_mul, hsdef, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq)
  set H : GL (Fin n) Ω := s * H₀ with hHdef
  have hHconj : ∀ Z, H * Z * H⁻¹ = H₀ * Z * H₀⁻¹ := fun Z => by
    calc H * Z * H⁻¹ = s * (H₀ * Z * H₀⁻¹) * s⁻¹ := by rw [hHdef]; group
      _ = H₀ * Z * H₀⁻¹ := by rw [hcent]; group
  have hHconj' : ∀ Z, H⁻¹ * Z * H = H₀⁻¹ * Z * H₀ := fun Z => by
    calc H⁻¹ * Z * H = H₀⁻¹ * (s⁻¹ * Z * s) * H₀ := by rw [hHdef]; group
      _ = H₀⁻¹ * Z * H₀ := by
        rw [show s⁻¹ * Z * s = s⁻¹ * (Z * s) by group, ← hcent Z]
        group
  have hconj : ∀ X, H⁻¹ * (A * τG (H * X * H⁻¹) * A⁻¹) * H = τG X := fun X => by
    rw [hHconj, hHconj', hconj₀]
  have hΦ : ∀ Z, A * τG Z * A⁻¹ = H * τG (H⁻¹ * Z * H) * H⁻¹ := fun Z => by
    rw [← hconj (H⁻¹ * Z * H)]
    group
  have hHdet : (H : Matrix (Fin n) (Fin n) Ω).det = 1 := by
    rw [hHdef, Units.val_mul, Matrix.det_mul, hsdef, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_mk0, hc, inv_mul_cancel₀ hH₀det]
  have hfixτ : ∀ Y : GL (Fin n) Ω, (Y : Matrix (Fin n) (Fin n) Ω).det = 1 →
      (τG Y = Y ↔ Y ∈ unitarySet (Ω := Ω) q n) := by
    intro Y hY
    have hkey : ((Y : Matrix (Fin n) (Fin n) Ω).map (· ^ q))ᵀ = (↑(τG Y)⁻¹ : Matrix _ _ Ω) := by
      rw [← hσG]
      rfl
    constructor
    · intro hτY
      refine ⟨fun i j => ?_, hY, ?_⟩
      · have h1 : σG (σG Y) = Y := by rw [← hττ, hτY, hτY]
        have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin n) Ω =>
          (g : Matrix (Fin n) (Fin n) Ω)) h1) i) j
        simp only [hσG, Matrix.map_apply] at h2
        rw [pow_two, pow_mul]
        exact h2
      · rw [hkey, hτY, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rintro ⟨-, -, hU⟩
      rw [hkey, ← Units.val_mul] at hU
      have h1 : (τG Y)⁻¹ * Y = 1 := Units.ext hU
      exact inv_mul_eq_one.mp h1
  refine ⟨H, hHdet, fun X _ => ?_, ?_⟩
  · have h1 : (H : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω) *
        (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) = ↑(H * X * H⁻¹) := by
      rw [← Units.val_mul, ← Units.val_mul]
    rw [h1, hτ, hτ, ← hconj X]
    simp only [Units.val_mul]
  · ext X
    constructor
    · rintro ⟨hXdet, hXfix⟩
      have hfix : A * τG X * A⁻¹ = X := by
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, ← hτ]
        exact hXfix
      refine ⟨H⁻¹ * X * H, ?_, by group⟩
      have hYdet : ((H⁻¹ * X * H : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hXdet, mul_one,
          ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      refine (hfixτ _ hYdet).mp ?_
      have h1 := hΦ X
      rw [hfix] at h1
      calc τG (H⁻¹ * X * H) = H⁻¹ * (H * τG (H⁻¹ * X * H) * H⁻¹) * H := by group
        _ = H⁻¹ * X * H := by rw [← h1]
    · rintro ⟨Y, hYU, rfl⟩
      have hYdet : (Y : Matrix (Fin n) (Fin n) Ω).det = 1 := hYU.2.1
      have hτY : τG Y = Y := (hfixτ Y hYdet).mpr hYU
      refine ⟨?_, ?_⟩
      · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hYdet, mul_one,
          ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      · rw [hτ, ← Units.val_mul, ← Units.val_mul, hΦ]
        congr 1
        rw [show H⁻¹ * (H * Y * H⁻¹) * H = Y by group, hτY]

end Descent

section Diagonal

variable {Ω : Type*} [Field Ω] {q n : ℕ}

theorem invTransposeHom_map_eq_iff_mem_unitarySet (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ q)
    {Y : GL (Fin n) Ω} (hY : (Y : Matrix (Fin n) (Fin n) Ω).det = 1) :
    invTransposeHom (Matrix.GeneralLinearGroup.map σ Y) = Y ↔
      Y ∈ unitarySet (Ω := Ω) q n := by
  classical
  let σG : GL (Fin n) Ω →* GL (Fin n) Ω := Matrix.GeneralLinearGroup.map σ
  let τG : GL (Fin n) Ω →* GL (Fin n) Ω := invTransposeHom.comp σG
  have hσG : ∀ X : GL (Fin n) Ω,
      (σG X : Matrix (Fin n) (Fin n) Ω) = (X : Matrix (Fin n) (Fin n) Ω).map (· ^ q) := by
    intro X
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hσ, Matrix.map_apply]
  have hττ : ∀ X, τG (τG X) = σG (σG X) := by
    intro X
    change invTransposeHom (σG (invTransposeHom (σG X))) = σG (σG X)
    rw [map_invTransposeHom, invTransposeHom_invTransposeHom]
  have hkey : ((Y : Matrix (Fin n) (Fin n) Ω).map (· ^ q))ᵀ =
      (↑(τG Y)⁻¹ : Matrix (Fin n) (Fin n) Ω) := by
    rw [← hσG]
    rfl
  have hiff : invTransposeHom (Matrix.GeneralLinearGroup.map σ Y) = Y ↔ τG Y = Y := Iff.rfl
  rw [hiff]
  constructor
  · intro hτY
    refine ⟨fun i j => ?_, hY, ?_⟩
    · have h1 : σG (σG Y) = Y := by rw [← hττ, hτY, hτY]
      have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin n) Ω =>
        (g : Matrix (Fin n) (Fin n) Ω)) h1) i) j
      simp only [hσG, Matrix.map_apply] at h2
      rw [pow_two, pow_mul]
      exact h2
    · rw [hkey, hτY, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rintro ⟨-, -, hU⟩
    rw [hkey, ← Units.val_mul] at hU
    have h1 : (τG Y)⁻¹ * Y = 1 := Units.ext hU
    exact inv_mul_eq_one.mp h1

theorem exists_diag_conj_invTransposeHom_of_diagonal [IsAlgClosed Ω] (hq : 1 ≤ q)
    (hn : 1 ≤ n) (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ q) (D : GL (Fin n) Ω)
    (d : Fin n → Ωˣ) (hD : (D : Matrix (Fin n) (Fin n) Ω) = diagonal (fun i => (d i : Ω))) :
    ∃ (H : GL (Fin n) Ω) (c : Ωˣ),
      (H : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
      (∀ i j : Fin n, i ≠ j → (H : Matrix (Fin n) (Fin n) Ω) i j = 0) ∧
      D = Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * H *
        (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹ := by
  classical
  have hn0 : 0 < n := by omega
  have hdetD : (D : Matrix (Fin n) (Fin n) Ω).det = ∏ i, (d i : Ω) := by
    rw [hD, Matrix.det_diagonal]
  have hdetD_ne : (D : Matrix (Fin n) (Fin n) Ω).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero D
  obtain ⟨c0, hc0pow⟩ := IsAlgClosed.exists_pow_nat_eq
    ((D : Matrix (Fin n) (Fin n) Ω).det)⁻¹ hn0
  have hc0 : c0 ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : n ≠ 0)] at hc0pow
    exact inv_ne_zero hdetD_ne hc0pow.symm
  have hc0det : c0 ^ n * (D : Matrix (Fin n) (Fin n) Ω).det = 1 := by
    rw [hc0pow, inv_mul_cancel₀ hdetD_ne]
  choose h hh using fun i => IsAlgClosed.exists_pow_nat_eq (c0 * (d i : Ω))
    (by omega : 0 < q + 1)
  have hne : ∀ i, h i ≠ 0 := by
    intro i hi
    have h1 : (0 : Ω) = c0 * (d i : Ω) := by
      rw [← hh i, hi, zero_pow (by omega : q + 1 ≠ 0)]
    exact (mul_ne_zero hc0 (d i).ne_zero) h1.symm
  set hprod : Ω := ∏ i, h i with hproddef
  have hprod_ne : hprod ≠ 0 := by
    rw [hproddef]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
  have hprod_pow : hprod ^ (q + 1) = 1 := by
    rw [hproddef, ← Finset.prod_pow]
    simp_rw [hh]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← hdetD, hc0det]
  set i0 : Fin n := ⟨0, hn0⟩ with hi0
  set g : Fin n → Ω := Function.update h i0 (h i0 / hprod) with hgdef
  have hg_pow : ∀ i, g i ^ (q + 1) = c0 * (d i : Ω) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rw [hgdef, Function.update_self, div_pow, hh i0, hprod_pow, div_one]
    · rw [hgdef, Function.update_of_ne hi, hh i]
  have hg_ne : ∀ i, g i ≠ 0 := by
    intro i hi
    have h1 : (0 : Ω) = c0 * (d i : Ω) := by
      rw [← hg_pow i, hi, zero_pow (by omega : q + 1 ≠ 0)]
    exact (mul_ne_zero hc0 (d i).ne_zero) h1.symm
  have hP_ne : (∏ i ∈ Finset.univ.erase i0, h i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
  have hprod_eq : hprod = h i0 * ∏ i ∈ Finset.univ.erase i0, h i := by
    rw [hproddef, ← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i0)]
  have hg_prod : (∏ i, g i) = 1 := by
    rw [hgdef, Finset.prod_update_of_mem (Finset.mem_univ i0), hprod_eq,
      Finset.sdiff_singleton_eq_erase i0 Finset.univ]
    field_simp
    exact div_self (hne i0)
  have hdetg : IsUnit (diagonal g : Matrix (Fin n) (Fin n) Ω).det := by
    rw [Matrix.det_diagonal, hg_prod]
    exact isUnit_one
  let H : GL (Fin n) Ω := Matrix.nonsingInvUnit (diagonal g) hdetg
  have hHcoe : (H : Matrix (Fin n) (Fin n) Ω) = diagonal g := rfl
  have hHdet : (H : Matrix (Fin n) (Fin n) Ω).det = 1 := by
    rw [hHcoe, Matrix.det_diagonal, hg_prod]
  have hHoff : ∀ i j : Fin n, i ≠ j → (H : Matrix (Fin n) (Fin n) Ω) i j = 0 := by
    intro i j hij
    rw [hHcoe, Matrix.diagonal_apply_ne _ hij]
  have hτH : invTransposeHom (Matrix.GeneralLinearGroup.map σ H) =
      (Matrix.GeneralLinearGroup.map σ H)⁻¹ := by
    apply Units.ext
    rw [coe_invTransposeHom, Matrix.GeneralLinearGroup.coe_inv]
    have hsymm : (((Matrix.GeneralLinearGroup.map σ H : GL (Fin n) Ω) :
        Matrix (Fin n) (Fin n) Ω))ᵀ =
        ((Matrix.GeneralLinearGroup.map σ H : GL (Fin n) Ω) :
          Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      rw [Matrix.transpose_apply, coe_generalLinearGroup_map, hHcoe,
        Matrix.diagonal_map (map_zero σ), Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        rfl
      · rw [if_neg hij, if_neg (Ne.symm hij)]
    rw [Matrix.transpose_nonsing_inv, hsymm]
  have hDH : H * (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c0 hc0) * D := by
    rw [hτH, inv_inv]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      hD, hHcoe, coe_generalLinearGroup_map, hHcoe, Matrix.diagonal_map (map_zero σ),
      Matrix.diagonal_mul_diagonal, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => g i * σ (g i)) = fun i => c0 * (d i : Ω) := by
      funext i
      rw [hσ, ← pow_succ', hg_pow]
    rw [hfun]
  refine ⟨H, Units.mk0 c0 hc0, hHdet, hHoff, ?_⟩
  have hs : Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c0 hc0)⁻¹ *
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c0 hc0) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [mul_assoc, hDH, ← mul_assoc, hs, one_mul]

end Diagonal

end CFSG.RankThree.Classical2
