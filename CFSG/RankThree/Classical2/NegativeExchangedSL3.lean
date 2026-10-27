module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.RankThree.Classical2

open Matrix
open scoped MatrixGroups

section InvTransposeMap

variable {Ω : Type*} [Field Ω] {n : ℕ}

@[expose] noncomputable def invTransposeMapSL (σ : Ω →+* Ω) (n : ℕ) : SL(n, Ω) →* SL(n, Ω) where
  toFun X := ⟨(((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ, by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, X.2, map_one, Ring.inverse_one]⟩
  map_one' := Subtype.ext (by
    change (((1 : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ = 1
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.inv_eq_left_inv (Matrix.mul_one 1),
      Matrix.transpose_one])
  map_mul' X Y := Subtype.ext (by
    change ((((X : Matrix (Fin n) (Fin n) Ω) * Y).map σ)⁻¹)ᵀ =
      (((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ * (((Y : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ
    rw [Matrix.map_mul, Matrix.mul_inv_rev, Matrix.transpose_mul])

theorem coe_invTransposeMapSL (σ : Ω →+* Ω) (X : SL(n, Ω)) :
    ((invTransposeMapSL σ n X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ :=
  rfl

theorem isUnit_det_map (ψ : Ω →+* Ω) (X : SL(n, Ω)) :
    IsUnit ((X : Matrix (Fin n) (Fin n) Ω).map ψ).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
  exact isUnit_one

theorem map_nonsing_inv_of_isUnit (ψ : Ω →+* Ω) {M : Matrix (Fin n) (Fin n) Ω}
    (hM : IsUnit M.det) : (M⁻¹).map ψ = (M.map ψ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hM, Matrix.map_one _ (map_zero ψ) (map_one ψ)]

theorem coe_invTransposeMapSL_invTransposeMapSL (σ : Ω →+* Ω) (X : SL(n, Ω)) :
    ((invTransposeMapSL σ n (invTransposeMapSL σ n X) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = (X : Matrix (Fin n) (Fin n) Ω).map (σ.comp σ) := by
  set W := ((X : Matrix (Fin n) (Fin n) Ω).map σ).map σ with hW
  have hWdet : IsUnit W.det := by
    rw [hW, Matrix.map_map]
    exact isUnit_det_map (σ.comp σ) X
  have e1 : ((((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ).map σ = (W⁻¹)ᵀ := by
    rw [Matrix.transpose_map, map_nonsing_inv_of_isUnit σ (isUnit_det_map σ X)]
  have e2 : ((W⁻¹)ᵀ)⁻¹ᵀ = W := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hWdet,
      Matrix.transpose_transpose]
  rw [coe_invTransposeMapSL, coe_invTransposeMapSL, e1, e2, hW, Matrix.map_map]
  rfl

end InvTransposeMap

section Frobenius

variable (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω] (n : ℕ)

@[expose] noncomputable def negFrobSL : SL(n, Ω) →* SL(n, Ω) :=
  invTransposeMapSL (FiniteField.frobeniusAlgHom k Ω : Ω →+* Ω) n

@[expose] def frobSqFixedField : Subfield Ω :=
  RingHom.eqLocusField ((FiniteField.frobeniusAlgHom k Ω : Ω →+* Ω).comp
    (FiniteField.frobeniusAlgHom k Ω : Ω →+* Ω)) (RingHom.id Ω)

variable {k Ω n}

theorem coe_negFrobSL (X : SL(n, Ω)) :
    ((negFrobSL k Ω n X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ Fintype.card k))⁻¹)ᵀ :=
  rfl

theorem mem_frobSqFixedField {c : Ω} :
    c ∈ frobSqFixedField k Ω ↔ c ^ (Fintype.card k ^ 2) = c := by
  change (c ^ Fintype.card k) ^ Fintype.card k = c ↔ _
  rw [← pow_mul, sq]

theorem coe_negFrobSL_negFrobSL (X : SL(n, Ω)) :
    ((negFrobSL k Ω n (negFrobSL k Ω n X) : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (X : Matrix (Fin n) (Fin n) Ω).map (· ^ (Fintype.card k ^ 2)) := by
  rw [negFrobSL, coe_invTransposeMapSL_invTransposeMapSL]
  congr 1
  funext c
  change (c ^ Fintype.card k) ^ Fintype.card k = c ^ (Fintype.card k ^ 2)
  rw [← pow_mul, sq]

theorem coe_negFrobSL_of_coe_eq_scalar {X : SL(n, Ω)} {c : Ω}
    (hX : (X : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c) (hc : c ≠ 0) :
    ((negFrobSL k Ω n X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      scalar (Fin n) (c ^ Fintype.card k)⁻¹ := by
  have hmap : (scalar (Fin n) c).map (· ^ Fintype.card k) =
      scalar (Fin n) (c ^ Fintype.card k) :=
    scalar_map (FiniteField.frobeniusAlgHom k Ω : Ω →+* Ω) c
  have hinv : (scalar (Fin n) (c ^ Fintype.card k))⁻¹ =
      scalar (Fin n) (c ^ Fintype.card k)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), map_one]
  rw [coe_negFrobSL, hX, hmap, hinv, Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem negFrobSL_negFrobSL_eq_self_iff (X : SL(n, Ω)) :
    negFrobSL k Ω n (negFrobSL k Ω n X) = X ↔
      ∃ A : SL(n, frobSqFixedField k Ω),
        Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype A = X := by
  constructor
  · intro h
    refine exists_map_eq_of_forall_mem_range Subtype.val_injective X fun i j =>
      ⟨⟨(X : Matrix (Fin n) (Fin n) Ω) i j, mem_frobSqFixedField.mpr ?_⟩, rfl⟩
    have := congrArg (fun Y : SL(n, Ω) => (Y : Matrix (Fin n) (Fin n) Ω) i j) h
    simpa only [coe_negFrobSL_negFrobSL, Matrix.map_apply] using this
  · rintro ⟨A, rfl⟩
    apply Subtype.ext
    rw [coe_negFrobSL_negFrobSL]
    ext i j
    rw [Matrix.map_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact mem_frobSqFixedField.mp (A i j).2

theorem natCard_frobSqFixedField [IsAlgClosure k Ω] :
    Nat.card (frobSqFixedField k Ω) = Fintype.card k ^ 2 := by
  obtain ⟨f, hℓ, hq⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hℓ⟩
  have : CharP Ω (ringChar k) := charP_of_injective_algebraMap (algebraMap k Ω).injective _
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have h2 : Fintype.card k ^ 2 = ringChar k ^ (2 * (f : ℕ)) := by rw [hq, ← pow_mul, mul_comm]
  rw [h2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ringChar k) (by have := f.pos; omega)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by rw [mem_frobSqFixedField, h2]; rfl)

theorem exists_mul_negFrobSL_negFrobSL_eq [IsAlgClosure k Ω] (hn : 1 ≤ n) (c₀ : SL(n, Ω)) :
    ∃ h : SL(n, Ω), c₀ * negFrobSL k Ω n (negFrobSL k Ω n h) = h := by
  obtain ⟨f, hℓ, hq⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hℓ⟩
  have : CharP Ω (ringChar k) := charP_of_injective_algebraMap (algebraMap k Ω).injective _
  have : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have h2 : Fintype.card k ^ 2 = ringChar k ^ (2 * (f : ℕ)) := by rw [hq, ← pow_mul, mul_comm]
  let K₂ : IntermediateField k Ω := Subfield.toIntermediateField (frobSqFixedField k Ω)
    fun x => by
      rw [mem_frobSqFixedField, ← map_pow, sq, pow_mul, FiniteField.pow_card,
        FiniteField.pow_card]
  have hcard : Nat.card K₂ = ringChar k ^ (2 * (f : ℕ)) := by
    rw [← h2, ← natCard_frobSqFixedField (k := k) (Ω := Ω)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)
  have : CharP K₂ (ringChar k) := charP_of_injective_algebraMap (algebraMap k K₂).injective _
  have : IsAlgClosure K₂ Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (K := K₂) (Ω := Ω) hℓ (by have := f.pos; omega)
    hcard hn (Matrix.SpecialLinearGroup.toGL c₀)
  obtain ⟨H, hHdet, hH⟩ := hlang c₀.2
  have hdet : (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω).det = 1 := by
    have := congrArg Matrix.det H.inv_mul
    rwa [Matrix.det_mul, hHdet, mul_one, Matrix.det_one] at this
  obtain ⟨h, hh⟩ : ∃ h : SL(n, Ω), (h : Matrix (Fin n) (Fin n) Ω) = ↑H⁻¹ := ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨h, Subtype.ext ?_⟩
  set ψ : Ω →+* Ω := iterateFrobenius Ω (ringChar k) (2 * (f : ℕ)) with hψ
  have hmap : ∀ M : Matrix (Fin n) (Fin n) Ω,
      M.map (· ^ (ringChar k ^ (2 * (f : ℕ)))) = M.map ψ := fun M => by
    congr 1
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_negFrobSL_negFrobSL, hh]
  change (Matrix.SpecialLinearGroup.toGL c₀ : Matrix (Fin n) (Fin n) Ω) *
      (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω).map (· ^ (Fintype.card k ^ 2)) = ↑H⁻¹
  rw [hH, h2, hmap, hmap, Matrix.mul_assoc, ← Matrix.map_mul, H.mul_inv,
    Matrix.map_one _ (map_zero ψ) (map_one ψ), Matrix.mul_one]

end Frobenius

section Scalar

variable (K : Type*) [Field K] (n : ℕ)

@[expose] def scalarSL : rootsOfUnity n K →* SL(n, K) where
  toFun ζ := ⟨scalar (Fin n) ((ζ : Kˣ) : K), by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n (ζ : Kˣ)).mp ζ.2,
      Units.val_one]⟩
  map_one' := Subtype.ext (by
    change scalar (Fin n) (((1 : rootsOfUnity n K) : Kˣ) : K) = 1
    rw [OneMemClass.coe_one, Units.val_one, map_one])
  map_mul' ζ η := Subtype.ext (by
    change scalar (Fin n) (((ζ * η : rootsOfUnity n K) : Kˣ) : K) =
      scalar (Fin n) ((ζ : Kˣ) : K) * scalar (Fin n) ((η : Kˣ) : K)
    rw [Subgroup.coe_mul, Units.val_mul, map_mul])

variable {K n}

theorem coe_scalarSL (ζ : rootsOfUnity n K) :
    ((scalarSL K n ζ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = scalar (Fin n) ((ζ : Kˣ) : K) :=
  rfl

theorem scalarSL_injective (hn : 1 ≤ n) : Function.Injective (scalarSL K n) := by
  intro ζ η h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := congrArg (fun A : SL(n, K) => (A : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_scalarSL, Matrix.scalar_inj] at h1
  exact Subtype.ext (Units.ext h1)

theorem mem_range_scalarSL_iff (hn : 1 ≤ n) (A : SL(n, K)) :
    A ∈ (scalarSL K n).range ↔
      ∃ c : K, c ^ n = 1 ∧ (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) c := by
  constructor
  · rintro ⟨ζ, rfl⟩
    refine ⟨((ζ : Kˣ) : K), ?_, rfl⟩
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n (ζ : Kˣ)).mp ζ.2, Units.val_one]
  · rintro ⟨c, hc, hA⟩
    have : NeZero n := ⟨by omega⟩
    exact ⟨rootsOfUnity.mkOfPowEq c hc,
      Subtype.ext (by rw [coe_scalarSL, rootsOfUnity.val_mkOfPowEq_coe, hA])⟩

theorem range_scalarSL (hn : 1 ≤ n) : (scalarSL K n).range = Subgroup.center SL(n, K) := by
  ext A
  rw [mem_range_scalarSL_iff hn, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

theorem natCard_center_specialLinearGroup [Finite K] (hn : 1 ≤ n) :
    Nat.card (Subgroup.center SL(n, K)) = Nat.gcd (Nat.card K - 1) n := by
  rw [← range_scalarSL hn, ← natCard_rootsOfUnity_eq_gcd n]
  exact Nat.card_congr (MonoidHom.ofInjective (scalarSL_injective hn)).toEquiv.symm

theorem natCard_rootsOfUnity_dvd (hn : 1 ≤ n) : Nat.card (rootsOfUnity n K) ∣ n := by
  have : NeZero n := ⟨by omega⟩
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ => Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity n (ζ : Kˣ)).mp ζ.2

theorem natCard_scalar_subgroup [Finite K] (hn : 1 ≤ n) (m : ℕ) (S : Subgroup SL(n, K))
    (hS : ∀ A, A ∈ S ↔ ∃ c : K, c ^ n = 1 ∧ c ^ m = 1 ∧
      (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) c) :
    Nat.card S = Nat.gcd (Nat.gcd (Nat.card K - 1) n) m := by
  have : NeZero n := ⟨by omega⟩
  have hS' : S = ((powMonoidHom m : rootsOfUnity n K →* rootsOfUnity n K).ker).map
      (scalarSL K n) := by
    ext A
    rw [hS, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hcn, hcm, hA⟩
      refine ⟨rootsOfUnity.mkOfPowEq c hcn, ?_, Subtype.ext ?_⟩
      · rw [MonoidHom.mem_ker, powMonoidHom_apply]
        apply Subtype.ext
        apply Units.ext
        rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.val_mkOfPowEq_coe, hcm]
        rfl
      · rw [coe_scalarSL, rootsOfUnity.val_mkOfPowEq_coe, hA]
    · rintro ⟨ζ, hζ, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hζ
      refine ⟨((ζ : Kˣ) : K), ?_, ?_, rfl⟩
      · rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n (ζ : Kˣ)).mp ζ.2, Units.val_one]
      · have := congrArg (fun x : rootsOfUnity n K => ((x : Kˣ) : K)) hζ
        simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
          Units.val_one] using this
  rw [hS', Subgroup.card_map_of_injective (scalarSL_injective hn), IsCyclic.card_powMonoidHom_ker,
    natCard_rootsOfUnity_eq_gcd]

theorem coe_conj_eq_scalar_iff {R : Type*} [CommRing R] (g Y : SL(n, R)) (c : R) :
    ((g * Y * g⁻¹ : SL(n, R)) : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c ↔
      (Y : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c := by
  refine ⟨fun h => ?_, coe_conj_eq_scalar g Y⟩
  have := coe_conj_eq_scalar g⁻¹ (g * Y * g⁻¹) h
  rwa [show g⁻¹ * (g * Y * g⁻¹) * g⁻¹⁻¹ = Y by group] at this

variable {k : Type*} [Field k] [Fintype k] {Ω : Type*} [Field Ω] [Algebra k Ω]

theorem negFrobSL_scalarSL (ζ : rootsOfUnity n Ω) :
    negFrobSL k Ω n (scalarSL Ω n ζ) = scalarSL Ω n (ζ ^ Fintype.card k)⁻¹ := by
  apply Subtype.ext
  rw [coe_negFrobSL_of_coe_eq_scalar (coe_scalarSL ζ) (Units.ne_zero _), coe_scalarSL]
  congr 1
  rw [InvMemClass.coe_inv, SubmonoidClass.coe_pow, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val]


theorem pow_eq_one_iff_of_coe_eq_scalar {R : Type*} [CommRing R] [Nontrivial R] (hn : 1 ≤ n)
    {A : SL(n, R)} {c : R} (hA : (A : Matrix (Fin n) (Fin n) R) = scalar (Fin n) c) (m : ℕ) :
    A ^ m = 1 ↔ c ^ m = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have key : A ^ m = 1 ↔ ((A ^ m : SL(n, R)) : Matrix (Fin n) (Fin n) R) =
      ((1 : SL(n, R)) : Matrix (Fin n) (Fin n) R) := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  rw [key, Matrix.SpecialLinearGroup.coe_pow, hA, ← map_pow,
    Matrix.SpecialLinearGroup.coe_one, ← map_one (scalar (Fin n)), Matrix.scalar_inj]

theorem gcd_gcd_sq_sub_one (n q : ℕ) :
    Nat.gcd (Nat.gcd (q ^ 2 - 1) n) (q + 1) = Nat.gcd n (q + 1) := by
  rw [Nat.gcd_assoc]
  refine Nat.gcd_eq_right ((Nat.gcd_dvd_right n (q + 1)).trans ?_)
  have h := Nat.sq_sub_sq q 1
  rw [one_pow] at h
  rw [h]
  exact Dvd.intro _ rfl

theorem negFrobSL_of_mem_center (hn : 1 ≤ n) {z : SL(n, Ω)}
    (hz : z ∈ Subgroup.center SL(n, Ω)) : negFrobSL k Ω n z = (z ^ Fintype.card k)⁻¹ := by
  rw [← range_scalarSL hn] at hz
  obtain ⟨ζ, rfl⟩ := hz
  rw [negFrobSL_scalarSL, map_inv, map_pow]

theorem exists_scalar_pair_iff (A B : SL(n, Ω)) :
    (∃ c : Ω, c ^ n = 1 ∧ (A : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c ∧
      (B : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c) ↔
        A = B ∧ A ∈ Subgroup.center SL(n, Ω) := by
  constructor
  · rintro ⟨c, hc, hA, hB⟩
    refine ⟨Subtype.ext (hA.trans hB.symm), Matrix.SpecialLinearGroup.mem_center_iff.mpr
      ⟨c, by rwa [Fintype.card_fin], hA.symm⟩⟩
  · rintro ⟨rfl, hA⟩
    obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hc
    exact ⟨c, hc, hcA.symm, hcA.symm⟩

end Scalar

structure NegExchangedLayer (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (Q : Type*) [Group Q] where
  μ : SL(n, Ω) × SL(n, Ω) →* Q
  surj : Function.Surjective μ
  ker_iff : ∀ A B, μ (A, B) = 1 ↔ A = B ∧ A ∈ Subgroup.center SL(n, Ω)
  θ : Q ≃* Q
  θ_μ : ∀ A B, θ (μ (A, B)) = μ (negFrobSL k Ω n B, negFrobSL k Ω n A)

namespace NegExchangedLayer

variable {k Ω : Type*} [Field k] [Fintype k] [Field Ω] [Algebra k Ω] {n : ℕ} {Q : Type*}
  [Group Q] (L : NegExchangedLayer k Ω n Q)

@[expose] noncomputable def layerMap : SL(n, frobSqFixedField k Ω) →* Q :=
  L.μ.comp ((Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype).prod
    ((negFrobSL k Ω n).comp (Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype)))

theorem layerMap_apply (A : SL(n, frobSqFixedField k Ω)) :
    L.layerMap A = L.μ (Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype A,
      negFrobSL k Ω n (Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype A)) :=
  rfl

theorem μ_eq_μ_iff {A B A' B' : SL(n, Ω)} : L.μ (A, B) = L.μ (A', B') ↔
    ∃ z ∈ Subgroup.center SL(n, Ω), A' = A * z ∧ B' = B * z := by
  have h1 : L.μ (A⁻¹ * A', B⁻¹ * B') = (L.μ (A, B))⁻¹ * L.μ (A', B') := by
    rw [← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk]
  rw [← inv_mul_eq_one, ← h1, L.ker_iff]
  constructor
  · rintro ⟨h, hz⟩
    exact ⟨A⁻¹ * A', hz, by group, by rw [h]; group⟩
  · rintro ⟨z, hz, rfl, rfl⟩
    rw [inv_mul_cancel_left, inv_mul_cancel_left]
    exact ⟨rfl, hz⟩

theorem μ_mem_fix_iff (A B : SL(n, Ω)) : L.μ (A, B) ∈ fixSubgroup L.θ ↔
    A⁻¹ * negFrobSL k Ω n B = B⁻¹ * negFrobSL k Ω n A ∧
      A⁻¹ * negFrobSL k Ω n B ∈ Subgroup.center SL(n, Ω) := by
  rw [mem_fixSubgroup, L.θ_μ, eq_comm, L.μ_eq_μ_iff]
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    rw [h1, h2, inv_mul_cancel_left, inv_mul_cancel_left]
    exact ⟨rfl, hz⟩
  · rintro ⟨h, hz⟩
    exact ⟨_, hz, by group, by rw [h]; group⟩

theorem layerMap_mem_fix (A : SL(n, frobSqFixedField k Ω)) :
    L.layerMap A ∈ fixSubgroup L.θ := by
  rw [layerMap_apply, mem_fixSubgroup, L.θ_μ, (negFrobSL_negFrobSL_eq_self_iff _).mpr ⟨A, rfl⟩]

theorem range_layerMap_le : L.layerMap.range ≤ fixSubgroup L.θ := by
  rintro _ ⟨A, rfl⟩
  exact L.layerMap_mem_fix A

theorem μ_mem_range_iff (hn : 1 ≤ n) {A B : SL(n, Ω)} (hfix : L.μ (A, B) ∈ fixSubgroup L.θ) :
    L.μ (A, B) ∈ L.layerMap.range ↔ ∃ w ∈ Subgroup.center SL(n, Ω),
      A⁻¹ * negFrobSL k Ω n B = w ^ (Fintype.card k + 1) := by
  obtain ⟨hAB, -⟩ := (L.μ_mem_fix_iff A B).mp hfix
  constructor
  · rintro ⟨C, hC⟩
    rw [layerMap_apply, L.μ_eq_μ_iff] at hC
    obtain ⟨z, hz, rfl, rfl⟩ := hC
    refine ⟨z⁻¹, inv_mem hz, ?_⟩
    rw [map_mul, (negFrobSL_negFrobSL_eq_self_iff _).mpr ⟨C, rfl⟩, negFrobSL_of_mem_center hn hz]
    group
  · rintro ⟨w, hw, hAw⟩
    have hτB : negFrobSL k Ω n B = A * w ^ (Fintype.card k + 1) := inv_mul_eq_iff_eq_mul.mp hAw
    have hτA : negFrobSL k Ω n A = B * w ^ (Fintype.card k + 1) := by
      rw [← hAw, hAB]
      group
    have hτw := negFrobSL_of_mem_center (k := k) hn hw
    have h1 : negFrobSL k Ω n (B * w) = A * w := by
      rw [map_mul, hτB, hτw]
      group
    have h2 : negFrobSL k Ω n (A * w) = B * w := by
      rw [map_mul, hτA, hτw]
      group
    obtain ⟨C, hC⟩ := (negFrobSL_negFrobSL_eq_self_iff (A * w)).mp (by rw [h2, h1])
    refine ⟨C, ?_⟩
    rw [layerMap_apply, hC, h2]
    exact (L.μ_eq_μ_iff.mpr ⟨w, hw, rfl, rfl⟩).symm

@[expose] noncomputable def discrepancy :
    (fixSubgroup L.θ).comap L.μ →* Subgroup.center SL(n, Ω) where
  toFun x := ⟨(x : SL(n, Ω) × SL(n, Ω)).1⁻¹ * negFrobSL k Ω n (x : SL(n, Ω) × SL(n, Ω)).2,
    ((L.μ_mem_fix_iff (x : SL(n, Ω) × SL(n, Ω)).1 (x : SL(n, Ω) × SL(n, Ω)).2).mp x.2).2⟩
  map_one' := Subtype.ext (by
    change (1 : SL(n, Ω))⁻¹ * negFrobSL k Ω n 1 = 1
    rw [map_one, inv_one, one_mul])
  map_mul' := by
    rintro ⟨⟨a₁, a₂⟩, hx⟩ ⟨⟨b₁, b₂⟩, hy⟩
    apply Subtype.ext
    have hz := ((L.μ_mem_fix_iff a₁ a₂).mp hx).2
    change (a₁ * b₁)⁻¹ * negFrobSL k Ω n (a₂ * b₂) =
      a₁⁻¹ * negFrobSL k Ω n a₂ * (b₁⁻¹ * negFrobSL k Ω n b₂)
    have hc := Subgroup.mem_center_iff.mp hz b₁⁻¹
    rw [map_mul, _root_.mul_inv_rev]
    calc b₁⁻¹ * a₁⁻¹ * (negFrobSL k Ω n a₂ * negFrobSL k Ω n b₂) =
        b₁⁻¹ * (a₁⁻¹ * negFrobSL k Ω n a₂) * negFrobSL k Ω n b₂ := by group
      _ = a₁⁻¹ * negFrobSL k Ω n a₂ * b₁⁻¹ * negFrobSL k Ω n b₂ := by rw [hc]
      _ = _ := by group

theorem coe_discrepancy (x : (fixSubgroup L.θ).comap L.μ) :
    ((L.discrepancy x : Subgroup.center SL(n, Ω)) : SL(n, Ω)) =
      (x : SL(n, Ω) × SL(n, Ω)).1⁻¹ * negFrobSL k Ω n (x : SL(n, Ω) × SL(n, Ω)).2 :=
  rfl

@[expose] noncomputable def discrepancyRoot (hn : 1 ≤ n) :
    (fixSubgroup L.θ).comap L.μ →* rootsOfUnity n Ω :=
  (MonoidHom.ofInjective (scalarSL_injective (K := Ω) hn)).symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr (range_scalarSL (K := Ω) hn)).symm.toMonoidHom.comp L.discrepancy)

theorem scalarSL_discrepancyRoot (hn : 1 ≤ n) (x : (fixSubgroup L.θ).comap L.μ) :
    scalarSL Ω n (L.discrepancyRoot hn x) =
      (x : SL(n, Ω) × SL(n, Ω)).1⁻¹ * negFrobSL k Ω n (x : SL(n, Ω) × SL(n, Ω)).2 := by
  set e := MonoidHom.ofInjective (scalarSL_injective (K := Ω) hn)
  have h := MonoidHom.ofInjective_apply (scalarSL_injective (K := Ω) hn)
    (x := L.discrepancyRoot hn x)
  change ((e (e.symm ((MulEquiv.subgroupCongr (range_scalarSL (K := Ω) hn)).symm
    (L.discrepancy x))) : (scalarSL Ω n).range) : SL(n, Ω)) = _ at h
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

@[expose] noncomputable def discrepancyClass (hn : 1 ≤ n) :
    (fixSubgroup L.θ).comap L.μ →* rootsOfUnity n Ω ⧸
      (powMonoidHom (Fintype.card k + 1) : rootsOfUnity n Ω →* rootsOfUnity n Ω).range :=
  (QuotientGroup.mk' _).comp (L.discrepancyRoot hn)

theorem discrepancyClass_eq_one_iff (hn : 1 ≤ n) (x : (fixSubgroup L.θ).comap L.μ) :
    L.discrepancyClass hn x = 1 ↔ L.μ x ∈ L.layerMap.range := by
  obtain ⟨⟨A, B⟩, hx⟩ := x
  rw [discrepancyClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    MonoidHom.mem_range]
  change _ ↔ L.μ (A, B) ∈ L.layerMap.range
  rw [L.μ_mem_range_iff hn hx]
  have hD := L.scalarSL_discrepancyRoot hn ⟨(A, B), hx⟩
  change scalarSL Ω n (L.discrepancyRoot hn ⟨(A, B), hx⟩) = A⁻¹ * negFrobSL k Ω n B at hD
  constructor
  · rintro ⟨ζ, hζ⟩
    refine ⟨scalarSL Ω n ζ, by rw [← range_scalarSL (K := Ω) hn]; exact ⟨ζ, rfl⟩, ?_⟩
    rw [← hD, ← hζ, powMonoidHom_apply, map_pow]
  · rintro ⟨w, hw, hAw⟩
    rw [← range_scalarSL (K := Ω) hn] at hw
    obtain ⟨ζ, rfl⟩ := hw
    refine ⟨ζ, scalarSL_injective hn ?_⟩
    rw [powMonoidHom_apply, map_pow, hD, hAw]

theorem comap_layerMap_range_eq (hn : 1 ≤ n) :
    (L.layerMap.range.subgroupOf (fixSubgroup L.θ)).comap (L.μ.subgroupComap (fixSubgroup L.θ)) =
      (L.discrepancyClass hn).ker := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.mem_ker,
    L.discrepancyClass_eq_one_iff hn]
  exact Iff.rfl

theorem subgroupComap_surjective :
    Function.Surjective (L.μ.subgroupComap (fixSubgroup L.θ)) :=
  MonoidHom.subgroupComap_surjective L.μ _ L.surj

theorem normal_layerMap_range (hn : 1 ≤ n) :
    (L.layerMap.range.subgroupOf (fixSubgroup L.θ)).Normal := by
  rw [← Subgroup.map_comap_eq_self_of_surjective L.subgroupComap_surjective
    (L.layerMap.range.subgroupOf (fixSubgroup L.θ)), L.comap_layerMap_range_eq hn]
  exact Subgroup.Normal.map (MonoidHom.normal_ker _) _ L.subgroupComap_surjective

theorem index_layerMap_range_dvd (hn : 1 ≤ n) :
    (L.layerMap.range.subgroupOf (fixSubgroup L.θ)).index ∣ Nat.gcd n (Fintype.card k + 1) := by
  have : NeZero n := ⟨by omega⟩
  rw [← Subgroup.index_comap_of_surjective _ L.subgroupComap_surjective,
    L.comap_layerMap_range_eq hn, Subgroup.index_ker]
  refine (Subgroup.card_subgroup_dvd_card _).trans ?_
  change Subgroup.index _ ∣ _
  rw [Subgroup.index_range, IsCyclic.card_powMonoidHom_ker]
  exact Nat.gcd_dvd_gcd_of_dvd_left _ (natCard_rootsOfUnity_dvd hn)

theorem commutator_mem_layerMap_range (hn : 1 ≤ n) {x y : Q} (hx : x ∈ fixSubgroup L.θ)
    (hy : y ∈ fixSubgroup L.θ) : x * y * x⁻¹ * y⁻¹ ∈ L.layerMap.range := by
  obtain ⟨x', hx'⟩ := L.subgroupComap_surjective ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := L.subgroupComap_surjective ⟨y, hy⟩
  have hc : L.discrepancyClass hn (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (L.discrepancyClass hn x')]
    group
  have h := (L.discrepancyClass_eq_one_iff hn _).mp hc
  have hx'' : L.μ (x' : SL(n, Ω) × SL(n, Ω)) = x := congrArg Subtype.val hx'
  have hy'' : L.μ (y' : SL(n, Ω) × SL(n, Ω)) = y := congrArg Subtype.val hy'
  have hxy : L.μ (x' * y' * x'⁻¹ * y'⁻¹ : (fixSubgroup L.θ).comap L.μ) = x * y * x⁻¹ * y⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      map_mul, map_mul, map_mul, map_inv, map_inv, hx'', hy'']
  rwa [← hxy]

theorem map_subtype_mem_center_iff (A : SL(n, frobSqFixedField k Ω)) :
    Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype A ∈
        Subgroup.center SL(n, Ω) ↔ A ∈ Subgroup.center SL(n, frobSqFixedField k Ω) := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h ⊢
    intro B
    apply specialLinearGroup_map_injective (frobSqFixedField k Ω).subtype.injective
    rw [map_mul, map_mul, h]
  · intro h
    obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(c : Ω), ?_, ?_⟩
    · rw [← SubmonoidClass.coe_pow, hc, OneMemClass.coe_one]
    · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← hcA, scalar_map]
      rfl

theorem layerMap_eq_one_iff (hn : 1 ≤ n) (A : SL(n, frobSqFixedField k Ω)) :
    L.layerMap A = 1 ↔ A ∈ Subgroup.center SL(n, frobSqFixedField k Ω) ∧
      A ^ (Fintype.card k + 1) = 1 := by
  have hι : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin n) (frobSqFixedField k Ω).subtype) :=
    specialLinearGroup_map_injective (frobSqFixedField k Ω).subtype.injective
  rw [layerMap_apply, L.ker_iff, map_subtype_mem_center_iff]
  constructor
  · rintro ⟨h, hz⟩
    refine ⟨hz, hι ?_⟩
    rw [map_pow, map_one, pow_succ']
    rw [negFrobSL_of_mem_center hn ((map_subtype_mem_center_iff A).mpr hz)] at h
    exact eq_inv_iff_mul_eq_one.mp h
  · rintro ⟨hz, hpow⟩
    refine ⟨?_, hz⟩
    rw [negFrobSL_of_mem_center hn ((map_subtype_mem_center_iff A).mpr hz),
      eq_inv_iff_mul_eq_one, ← pow_succ', ← map_pow, hpow, map_one]

theorem layerMap_eq_one_iff_scalar (hn : 1 ≤ n) (A : SL(n, frobSqFixedField k Ω)) :
    L.layerMap A = 1 ↔ ∃ c : frobSqFixedField k Ω, c ^ n = 1 ∧ c ^ (Fintype.card k + 1) = 1 ∧
      (A : Matrix (Fin n) (Fin n) (frobSqFixedField k Ω)) = scalar (Fin n) c := by
  rw [L.layerMap_eq_one_iff hn, ← range_scalarSL hn, mem_range_scalarSL_iff hn]
  constructor
  · rintro ⟨⟨c, hc, hA⟩, hp⟩
    exact ⟨c, hc, (pow_eq_one_iff_of_coe_eq_scalar hn hA _).mp hp, hA⟩
  · rintro ⟨c, hc, hcm, hA⟩
    exact ⟨⟨c, hc, hA⟩, (pow_eq_one_iff_of_coe_eq_scalar hn hA _).mpr hcm⟩

theorem finite_frobSqFixedField [IsAlgClosure k Ω] : Finite (frobSqFixedField k Ω) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_frobSqFixedField]
    exact pow_ne_zero 2 Fintype.card_ne_zero)

theorem natCard_ker_layerMap [IsAlgClosure k Ω] (hn : 1 ≤ n) :
    Nat.card L.layerMap.ker = Nat.gcd n (Fintype.card k + 1) := by
  have := finite_frobSqFixedField (k := k) (Ω := Ω)
  rw [natCard_scalar_subgroup hn (Fintype.card k + 1) L.layerMap.ker
      (fun A => by rw [MonoidHom.mem_ker, L.layerMap_eq_one_iff_scalar hn]),
    natCard_frobSqFixedField, gcd_gcd_sq_sub_one]

theorem isQuasisimple_range_layerMap (hn : 3 ≤ n) : CFSG.IsQuasisimple L.layerMap.range := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (isQuasisimple_specialLinearGroup hn) L.layerMap.rangeRestrict_surjective ?_
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨Matrix.SpecialLinearGroup.transvection h01 1, fun h => ?_⟩
  have h' : L.layerMap (Matrix.SpecialLinearGroup.transvection h01 1) = 1 :=
    congrArg Subtype.val h
  obtain ⟨hz, -⟩ := (L.layerMap_eq_one_iff (by omega) _).mp h'
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [Matrix.SpecialLinearGroup.transvection_coe] at h1
  simp at h1

theorem center_range_layerMap (hn : 3 ≤ n) :
    Subgroup.center L.layerMap.range =
      (Subgroup.center SL(n, frobSqFixedField k Ω)).map L.layerMap.rangeRestrict :=
  CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (isQuasisimple_specialLinearGroup hn) L.layerMap.rangeRestrict_surjective (by
      intro A hA
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, L.layerMap_eq_one_iff (by omega)] at hA
      exact hA.1)

theorem natCard_center_range_layerMap [IsAlgClosure k Ω] (hn : 3 ≤ n) :
    Nat.card (Subgroup.center L.layerMap.range) =
      Nat.gcd n (Fintype.card k ^ 2 - 1) / Nat.gcd n (Fintype.card k + 1) := by
  have := finite_frobSqFixedField (k := k) (Ω := Ω)
  set Z := Subgroup.center SL(n, frobSqFixedField k Ω) with hZ
  let f : Z →* L.layerMap.range := L.layerMap.rangeRestrict.comp Z.subtype
  have hrange : f.range = Subgroup.center L.layerMap.range := by
    rw [L.center_range_layerMap hn, MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : L.layerMap.ker ≤ Z := fun A hA => ((L.layerMap_eq_one_iff (by omega) A).mp hA).1
  have hker : f.ker = L.layerMap.ker.subgroupOf Z := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hrange,
    L.natCard_ker_layerMap (by omega), hZ, natCard_center_specialLinearGroup (by omega),
    natCard_frobSqFixedField] at hmul
  rw [Nat.gcd_comm n (Fintype.card k ^ 2 - 1)]
  exact (Nat.div_eq_of_eq_mul_right (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _))
    hmul.symm).symm

theorem finite_fix [IsAlgClosure k Ω] (hn : 1 ≤ n) : Finite (fixSubgroup L.θ) := by
  have := finite_frobSqFixedField (k := k) (Ω := Ω)
  have hP : Nat.card (L.layerMap.range.subgroupOf (fixSubgroup L.θ)) ≠ 0 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe L.range_layerMap_le).toEquiv]
    have : Finite L.layerMap.range := Finite.of_surjective _ L.layerMap.rangeRestrict_surjective
    exact Nat.card_pos.ne'
  have hidx : (L.layerMap.range.subgroupOf (fixSubgroup L.θ)).index ≠ 0 := by
    intro h
    have h1 := L.index_layerMap_range_dvd hn
    rw [h, zero_dvd_iff] at h1
    exact (Nat.gcd_pos_of_pos_left _ (by omega)).ne' h1
  apply Nat.finite_of_card_ne_zero
  rw [← Subgroup.card_mul_index (L.layerMap.range.subgroupOf (fixSubgroup L.θ))]
  exact mul_ne_zero hP hidx

theorem commutator_fix (hn : 3 ≤ n) :
    ⁅fixSubgroup L.θ, fixSubgroup L.θ⁆ = L.layerMap.range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact L.commutator_mem_layerMap_range (by omega) hx hy
  · have : Group.IsPerfect SL(n, frobSqFixedField k Ω) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
    have : Group.IsPerfect L.layerMap.range := Group.IsPerfect.range L.layerMap
    calc L.layerMap.range = ⁅L.layerMap.range, L.layerMap.range⁆ :=
          Subgroup.commutator_eq_self.symm
      _ ≤ _ := Subgroup.commutator_mono L.range_layerMap_le L.range_layerMap_le

end NegExchangedLayer

section FixedLayer

variable {k : Type*} [Field k] [Finite k] {q : ℕ} {Ω : Type*} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

theorem negative_exchanged_SLn_fixed_layer (hk : Nat.card k = q) (k₂ : Subfield Ω)
    (hk₂ : ∀ c : Ω, c ∈ k₂ ↔ c ^ q ^ 2 = c) {n : ℕ} (hn : 3 ≤ n) (τ : SL(n, Ω) → SL(n, Ω))
    (hτ : ∀ X : SL(n, Ω), ((τ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ q))⁻¹)ᵀ)
    {Q : Type*} [Group Q] (μ : SL(n, Ω) × SL(n, Ω) →* Q) (hμ : Function.Surjective μ)
    (hker : ∀ A B : SL(n, Ω), μ (A, B) = 1 ↔ ∃ c : Ω, c ^ n = 1 ∧
      (A : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c ∧
        (B : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c)
    (θ : Q ≃* Q) (a b : SL(n, Ω))
    (hθ : ∀ A B : SL(n, Ω), θ (μ (A, B)) = μ (a * τ B * a⁻¹, b * τ A * b⁻¹)) :
    ∃ h₁ h₂ : SL(n, Ω), ∃ ψ : SL(n, k₂) →* Q,
      (∀ A : SL(n, k₂), ψ A = μ (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * τ (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)) ∧
      ψ.range ≤ fixSubgroup θ ∧ (ψ.range.subgroupOf (fixSubgroup θ)).Normal ∧
      CFSG.IsQuasisimple ψ.range ∧
      (∀ A : SL(n, k₂), ψ A = 1 ↔ ∃ c : k₂, c ^ n = 1 ∧ c ^ (q + 1) = 1 ∧
        (A : Matrix (Fin n) (Fin n) k₂) = scalar (Fin n) c) ∧
      Nat.card ψ.ker = Nat.gcd n (q + 1) ∧
      Subgroup.center ψ.range = (Subgroup.center SL(n, k₂)).map ψ.rangeRestrict ∧
      Nat.card (Subgroup.center ψ.range) = Nat.gcd n (q ^ 2 - 1) / Nat.gcd n (q + 1) ∧
      Finite (fixSubgroup θ) ∧
      (∀ x ∈ fixSubgroup θ, ∀ y ∈ fixSubgroup θ, x * y * x⁻¹ * y⁻¹ ∈ ψ.range) ∧
      (ψ.range.subgroupOf (fixSubgroup θ)).index ∣ Nat.gcd n (q + 1) ∧
      ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range := by
  have := Fintype.ofFinite k
  have hq : Fintype.card k = q := by rw [← Nat.card_eq_fintype_card, hk]
  subst hq
  obtain rfl : k₂ = frobSqFixedField k Ω := by
    ext c
    rw [hk₂, mem_frobSqFixedField]
  obtain rfl : τ = ⇑(negFrobSL k Ω n) := funext fun X => Subtype.ext (by rw [hτ, coe_negFrobSL])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h₁, hh₁⟩ := exists_mul_negFrobSL_negFrobSL_eq (k := k) hn1 (a * negFrobSL k Ω n b)
  obtain ⟨h₂, hh₂def⟩ : ∃ h₂ : SL(n, Ω), h₂ = b * negFrobSL k Ω n h₁ := ⟨_, rfl⟩
  have hh₂ : a * negFrobSL k Ω n h₂ = h₁ := by
    rw [hh₂def, map_mul, ← mul_assoc]
    exact hh₁
  let μ' : SL(n, Ω) × SL(n, Ω) →* Q :=
    μ.comp ((MulAut.conj h₁).toMonoidHom.prodMap (MulAut.conj h₂).toMonoidHom)
  have hμ' : ∀ A B, μ' (A, B) = μ (h₁ * A * h₁⁻¹, h₂ * B * h₂⁻¹) := fun A B => rfl
  let L : NegExchangedLayer k Ω n Q :=
    { μ := μ'
      surj := by
        intro x
        obtain ⟨⟨A, B⟩, rfl⟩ := hμ x
        refine ⟨(h₁⁻¹ * A * h₁, h₂⁻¹ * B * h₂), ?_⟩
        rw [hμ']
        congr 2 <;> group
      ker_iff := fun A B => by
        rw [hμ', hker, ← exists_scalar_pair_iff]
        simp only [coe_conj_eq_scalar_iff]
      θ := θ
      θ_μ := fun A B => by
        rw [hμ', hμ', hθ]
        simp only [map_mul, map_inv]
        have e1 : a * (negFrobSL k Ω n h₂ * negFrobSL k Ω n B * (negFrobSL k Ω n h₂)⁻¹) * a⁻¹ =
            h₁ * negFrobSL k Ω n B * h₁⁻¹ := by
          rw [← hh₂]
          group
        have e2 : b * (negFrobSL k Ω n h₁ * negFrobSL k Ω n A * (negFrobSL k Ω n h₁)⁻¹) * b⁻¹ =
            h₂ * negFrobSL k Ω n A * h₂⁻¹ := by
          rw [hh₂def]
          group
        rw [e1, e2] }
  refine ⟨h₁, h₂, L.layerMap, fun A => rfl, L.range_layerMap_le, L.normal_layerMap_range hn1,
    L.isQuasisimple_range_layerMap hn, L.layerMap_eq_one_iff_scalar hn1,
    L.natCard_ker_layerMap hn1, L.center_range_layerMap hn, L.natCard_center_range_layerMap hn,
    L.finite_fix hn1, fun x hx y hy => L.commutator_mem_layerMap_range hn1 hx hy,
    L.index_layerMap_range_dvd hn1, L.commutator_fix hn⟩

theorem negative_exchanged_SL3_central_product_fixed_layer (hk : Nat.card k = q)
    (k₂ : Subfield Ω) (hk₂ : ∀ c : Ω, c ∈ k₂ ↔ c ^ q ^ 2 = c) (τ : SL(3, Ω) → SL(3, Ω))
    (hτ : ∀ X : SL(3, Ω), ((τ X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      (((X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ q))⁻¹)ᵀ)
    {Q : Type*} [Group Q] (μ : SL(3, Ω) × SL(3, Ω) →* Q) (hμ : Function.Surjective μ)
    (hker : ∀ A B : SL(3, Ω), μ (A, B) = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c ∧
        (B : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c)
    (θ : Q ≃* Q) (a b : SL(3, Ω))
    (hθ : ∀ A B : SL(3, Ω), θ (μ (A, B)) = μ (a * τ B * a⁻¹, b * τ A * b⁻¹)) :
    ∃ h₁ h₂ : SL(3, Ω), ∃ ψ : SL(3, k₂) →* Q,
      (∀ A : SL(3, k₂), ψ A = μ (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * τ (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)) ∧
      ψ.range ≤ fixSubgroup θ ∧ (ψ.range.subgroupOf (fixSubgroup θ)).Normal ∧
      CFSG.IsQuasisimple ψ.range ∧
      (∀ A : SL(3, k₂), ψ A = 1 ↔ ∃ c : k₂, c ^ 3 = 1 ∧ c ^ (q + 1) = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) k₂) = scalar (Fin 3) c) ∧
      Nat.card ψ.ker = Nat.gcd 3 (q + 1) ∧
      Subgroup.center ψ.range = (Subgroup.center SL(3, k₂)).map ψ.rangeRestrict ∧
      Nat.card (Subgroup.center ψ.range) = Nat.gcd 3 (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      Finite (fixSubgroup θ) ∧
      (∀ x ∈ fixSubgroup θ, ∀ y ∈ fixSubgroup θ, x * y * x⁻¹ * y⁻¹ ∈ ψ.range) ∧
      (ψ.range.subgroupOf (fixSubgroup θ)).index ∣ Nat.gcd 3 (q + 1) ∧
      ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range :=
  negative_exchanged_SLn_fixed_layer hk k₂ hk₂ le_rfl τ hτ μ hμ hker θ a b hθ

end FixedLayer

end CFSG.RankThree.Classical2
