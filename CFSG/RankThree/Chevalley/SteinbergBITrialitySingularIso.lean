module

public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularFix
public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularSL3

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 CFSG.RankThree.SL3RootPermuting Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped Matrix Pointwise MatrixGroups

variable {Ω : Type} [Field Ω]

theorem threeSix_stab [IsAlgClosed Ω] {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {a : Fin TwistTag.D4.tag.rank → Ωˣ}
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε) {v : WeylGroup Tag.D4}
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a) :
    ∀ α ∈ (fun β => v • β) '' d4A2Sigma, tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma := by
  have hchar := (rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε a).1 ha
  have hW : (ε • twelveW ^ 4 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) =
      tsW ε := (threeSixW_eq_smul hε).symm
  intro α hα
  rw [hv] at hα ⊢
  obtain ⟨hroot, h1⟩ := hα
  refine ⟨isRoot_tsW_mulVec ε hroot, ?_⟩
  have h := hchar α
  rw [hW] at h
  exact h.trans (by rw [h1, one_pow])

@[expose] def threeSixL (ε : ℤ) (v : WeylGroup Tag.D4) :
    (Fin Tag.D4.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ) :=
  AddMonoidHom.mk' (fun β => v⁻¹ • (tsW ε *ᵥ (v • β))) fun β γ => by
    rw [smul_add, Matrix.mulVec_add, smul_add]

theorem smul_threeSixL (ε : ℤ) (v : WeylGroup Tag.D4) (β : Fin Tag.D4.rank → ℤ) :
    v • threeSixL ε v β = tsW ε *ᵥ (v • β) :=
  smul_inv_smul v _

theorem threeSixL_mem {ε : ℤ} {v : WeylGroup Tag.D4}
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    ∀ β ∈ d4Sigma0List, threeSixL ε v β ∈ d4Sigma0List := by
  intro β hβ
  rw [← mem_d4A2Sigma_iff] at hβ ⊢
  obtain ⟨γ, hγ, hγβ⟩ := hstab _ ⟨β, hβ, rfl⟩
  have : threeSixL ε v β = γ := by
    apply MulAction.injective v
    change v • threeSixL ε v β = v • γ
    rw [smul_threeSixL]
    exact hγβ.symm
  rw [this]
  exact hγ

theorem threeSixL_quad {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (β : Fin Tag.D4.rank → ℤ) :
    threeSixL ε v (threeSixL ε v β) + ε • threeSixL ε v β + β = 0 := by
  apply MulAction.injective v
  change v • (threeSixL ε v (threeSixL ε v β) + ε • threeSixL ε v β + β) = v • (0 : _)
  rw [smul_add, smul_add, smul_threeSixL, smul_threeSixL, smul_comm, smul_threeSixL, smul_zero]
  have h := congrArg (fun A : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ => A *ᵥ (v • β))
    (threeSixW_mul_add hε)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
    ← Matrix.mulVec_mulVec] at h
  exact h

theorem threeSix_phi_split (Fr : Ω →+* Ω) (hFrs : Function.Surjective Fr) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW 1 *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    ∃ π : Equiv.Perm (Fin 3), ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((threeSixPhi Ω Fr hFrs (Or.inl rfl) v hstab (SpecialLinearGroup.transvection hij t) :
        SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_sq_add_add_one (threeSixL 1 v) (threeSixL_mem hstab)
    fun β _ => by
      have h := threeSixL_quad (Or.inl rfl) v β
      rwa [one_smul] at h
  have hWv : ∀ i j : Fin 3, i ≠ j →
      tsW 1 *ᵥ (v • chainRoot d4ChainA2 i j) = v • chainRoot d4ChainA2 (π i) (π j) :=
    fun i j _ => by rw [← smul_threeSixL, hπ]
  obtain ⟨b, hb⟩ := exists_threeSixPhi_transvection Fr hFrs (Or.inl rfl) v hstab
    (fun i _ => π i) (fun _ j => π j) (fun _ _ hij => π.injective.ne hij) hWv
  exact ⟨π, b, hb⟩

theorem threeSix_phi_unitary (Fr : Ω →+* Ω) (hFrs : Function.Surjective Fr)
    (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW (-1) *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    ∃ π : Equiv.Perm (Fin 3), ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((threeSixPhi Ω Fr hFrs (Or.inr rfl) v hstab (SpecialLinearGroup.transvection hij t) :
        SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * Fr t) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_sq_sub_add_one (threeSixL (-1) v) (threeSixL_mem hstab)
    fun β _ => by
      have h := threeSixL_quad (Or.inr rfl) v β
      rwa [neg_one_smul, ← sub_eq_add_neg] at h
  have hWv : ∀ i j : Fin 3, i ≠ j →
      tsW (-1) *ᵥ (v • chainRoot d4ChainA2 i j) = v • chainRoot d4ChainA2 (π j) (π i) :=
    fun i j _ => by rw [← smul_threeSixL, hπ]
  obtain ⟨b, hb⟩ := exists_threeSixPhi_transvection Fr hFrs (Or.inr rfl) v hstab
    (fun _ j => π j) (fun i _ => π i) (fun _ _ hij => π.injective.ne hij.symm) hWv
  exact ⟨π, b, hb⟩

theorem natCard_eqLocusField_D4 {K : Type} [Field K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f := by
  have h := card_orbitField_D4_orientation hℓ hf hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) ⟨1, by decide⟩
  have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  rw [h1, pow_one] at h
  have e : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =
      RingHom.eqLocusField σ.toRingHom (RingHom.id K) := by
    ext c
    rw [mem_orbitField, h1, pow_one, RingHom.mem_eqLocusField, RingHom.id_apply]
  rw [← e]
  exact h

theorem natCard_eqLocusField_frob [IsAlgClosed Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    [CharP Ω ℓ] {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Nat.card (RingHom.eqLocusField Fr (RingHom.id Ω)) = ℓ ^ f := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have e : RingHom.eqLocusField Fr (RingHom.id Ω) = frobeniusFixedField Ω ℓ f := by
    ext c
    rw [RingHom.mem_eqLocusField, mem_frobeniusFixedField, hFr, RingHom.id_apply]
  rw [e]
  exact card_frobeniusFixedField (by omega)

variable (Ω) in
@[expose] def threeSixRΩ (Fr : Ω →+* Ω) (ε : ℤ) (v : WeylGroup Tag.D4) :
    Subgroup (ModGL TwistTag.D4.tag Ω) :=
  tsQv Ω v ⊓ (threeSixFrob Ω Fr ε).eqLocus (MonoidHom.id _)

@[expose] def tsQvEquiv (v : WeylGroup Tag.D4) : tsQv Ω v ≃* SL(3, Ω) := d4A2QvEquiv v

theorem threeSixRΩ_le (Fr : Ω →+* Ω) (ε : ℤ) (v : WeylGroup Tag.D4) :
    threeSixRΩ Ω Fr ε v ≤ tsQv Ω v :=
  inf_le_left

@[expose] def threeSixRΩEquivFix (Fr : Ω →+* Ω) (hFrs : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    threeSixRΩ Ω Fr ε v ≃* fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab) :=
  MulEquiv.ofBijective
    (((tsQvEquiv v).toMonoidHom.comp (Subgroup.inclusion (threeSixRΩ_le Fr ε v))).codRestrict
      (fixSubgroup (threeSixPhi Ω Fr hFrs hε v hstab)) fun u => by
        rw [mem_fixSubgroup_threeSixPhi]
        change tsFrob Ω Fr ε (((d4A2QvEquiv v).symm (d4A2QvEquiv v ⟨u.1, u.2.1⟩) :
            d4A2Qv Ω v) : ModGL Tag.D4 Ω) =
          (((d4A2QvEquiv v).symm (d4A2QvEquiv v ⟨u.1, u.2.1⟩) : d4A2Qv Ω v) : ModGL Tag.D4 Ω)
        rw [MulEquiv.symm_apply_apply]
        exact u.2.2)
    ⟨fun u w h => Subgroup.inclusion_injective (threeSixRΩ_le Fr ε v)
      ((tsQvEquiv v).injective (congrArg Subtype.val h)), fun X => by
        set Y := (tsQvEquiv (Ω := Ω) v).symm (X : SL(3, Ω)) with hY
        refine ⟨⟨(Y : ModGL TwistTag.D4.tag Ω), Subgroup.mem_inf.2 ⟨Y.2, ?_⟩⟩, Subtype.ext ?_⟩
        · exact (mem_fixSubgroup_threeSixPhi Fr hFrs hε v hstab X).1 X.2
        · change tsQvEquiv v ⟨_, _⟩ = (X : SL(3, Ω))
          exact (tsQvEquiv v).apply_symm_apply (X : SL(3, Ω))⟩

section FieldEquiv

variable {K : Type} [Field K] [Algebra K Ω]

@[expose] def threeSixFieldHom {q : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ q) :
    RingHom.eqLocusField σ.toRingHom (RingHom.id K) →+* RingHom.eqLocusField Fr (RingHom.id Ω) :=
  ((algebraMap K Ω).comp (RingHom.eqLocusField σ.toRingHom (RingHom.id K)).subtype).codRestrict
    _ fun c => by
      have hc : σ c = c := c.2
      rw [RingHom.mem_eqLocusField, RingHom.id_apply, RingHom.comp_apply, hFr, ← map_pow,
        ← hσ]
      exact congrArg _ hc

@[expose] def threeSixFieldEquiv {q : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ q)
    (h₀ : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = q)
    (h₁ : Nat.card (RingHom.eqLocusField Fr (RingHom.id Ω)) = q) (hq : q ≠ 0) :
    RingHom.eqLocusField σ.toRingHom (RingHom.id K) ≃+* RingHom.eqLocusField Fr (RingHom.id Ω) :=
  RingEquiv.ofBijective (threeSixFieldHom hσ hFr) (by
    have : Finite (RingHom.eqLocusField Fr (RingHom.id Ω)) :=
      Nat.finite_of_card_ne_zero (by rw [h₁]; exact hq)
    exact (Nat.bijective_iff_injective_and_card _).2
      ⟨(threeSixFieldHom hσ hFr).injective, by rw [h₀, h₁]⟩)

theorem coe_threeSixFieldEquiv {q : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ q)
    (h₀ : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = q)
    (h₁ : Nat.card (RingHom.eqLocusField Fr (RingHom.id Ω)) = q) (hq : q ≠ 0)
    (c : RingHom.eqLocusField σ.toRingHom (RingHom.id K)) :
    (threeSixFieldEquiv hσ hFr h₀ h₁ hq c : Ω) = algebraMap K Ω c :=
  rfl

end FieldEquiv

section Fix

variable {K : Type} [Field K] [Algebra K Ω] [IsAlgClosure K Ω]

@[expose] def slMapEquiv {A B : Type} [Field A] [Field B] (E : A ≃+* B) :
    SL(3, A) ≃* SL(3, B) where
  toFun := SpecialLinearGroup.map E.toRingHom
  invFun := SpecialLinearGroup.map E.symm.toRingHom
  left_inv Y := Subtype.ext (by ext i j; simp)
  right_inv Y := Subtype.ext (by ext i j; simp)
  map_mul' := map_mul _

theorem setup_k₀ {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    IsAlgClosure (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) Ω ∧
      Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  set k₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id K)
  have : Module.Finite k₀ K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k₀ K := Algebra.IsAlgebraic.of_finite k₀ K
  exact ⟨IsAlgClosure.ofAlgebraic k₀ K Ω, natCard_eqLocusField_D4 hℓ hf hK hσ⟩

omit [IsAlgClosure K Ω] in
theorem charP_of_card_cube {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3) :
    CharP Ω ℓ := by
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  exact charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ

omit [IsAlgClosure K Ω] in
theorem map_algebraMap_eq {ℓ f : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (h₀ : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f)
    (h₁ : Nat.card (RingHom.eqLocusField Fr (RingHom.id Ω)) = ℓ ^ f) (hq : ℓ ^ f ≠ 0)
    (A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω))) :
    SpecialLinearGroup.map (algebraMap (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) Ω)
        (SpecialLinearGroup.map (threeSixFieldEquiv hσ hFr h₀ h₁ hq).symm.toRingHom A) =
      SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A := by
  refine Subtype.ext ?_
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [IsScalarTower.algebraMap_apply _ K Ω]
  have h := coe_threeSixFieldEquiv hσ hFr h₀ h₁ hq
    ((threeSixFieldEquiv hσ hFr h₀ h₁ hq).symm ((A : Matrix (Fin 2) (Fin 2) _) i j))
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem threeSix_fix_split {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (Φ : SL(3, Ω) ≃* SL(3, Ω)) (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Ωˣ)
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (SpecialLinearGroup.transvection hij t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single (π i) (π j) ((b i j : Ω) * Fr t)) :
    Nonempty (fixSubgroup Φ ≃* SL(3, RingHom.eqLocusField Fr (RingHom.id Ω))) ∧
    CFSG.IsQuasisimple (fixSubgroup Φ) ∧
    Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd 3 (ℓ ^ f - 1) ∧
    ∃ J : SL(3, Ω), ∀ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)),
      J * (blockSL Ω 2 1 (SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype
        A) : SL(3, Ω)) * J⁻¹ ∈ fixSubgroup Φ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  have h₁ := natCard_eqLocusField_frob hℓ hf hFr
  have hq : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  set k₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id K)
  obtain ⟨-, ⟨H, hH⟩, ⟨J, hJ⟩, -, hQ, -, hcard, -⟩ := sl3_root_permuting_frobenius_fixed_split
    (k := k₀) hℓ hf h₀ π Φ b fun i j hij t => by rw [hΦ, hFr]
  let e₀ : SL(3, k₀) →* fixSubgroup Φ :=
    { toFun := fun Y => ⟨H * SpecialLinearGroup.map (algebraMap k₀ Ω) Y * H⁻¹, (hH _).2 ⟨Y, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun Y Z => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro Y Z hYZ
      have h1 := congrArg Subtype.val hYZ
      change H * _ * H⁻¹ = H * _ * H⁻¹ at h1
      rw [mul_left_inj, mul_right_inj] at h1
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      have h2 := congrArg (fun X : SL(3, Ω) => (X : Matrix (Fin 3) (Fin 3) Ω) i j) h1
      simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h2
      exact (algebraMap k₀ Ω).injective h2
    · intro X
      obtain ⟨Y, hY⟩ := (hH X).1 X.2
      exact ⟨Y, Subtype.ext hY.symm⟩
  refine ⟨⟨(MulEquiv.ofBijective e₀ he₀).symm.trans
      (slMapEquiv (threeSixFieldEquiv hσ hFr h₀ h₁ hq))⟩, hQ, hcard, J, fun A => ?_⟩
  have h := hJ (SpecialLinearGroup.map (threeSixFieldEquiv hσ hFr h₀ h₁ hq).symm.toRingHom A)
  rwa [map_algebraMap_eq hσ hFr h₀ h₁ hq] at h

theorem threeSix_fix_unitary {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (hq2 : 2 < ℓ ^ f)
    (Φ : SL(3, Ω) ≃* SL(3, Ω)) (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Ωˣ)
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (SpecialLinearGroup.transvection hij t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single (π j) (π i) ((b i j : Ω) * Fr t)) :
    (∃ U : Subgroup (GL (Fin 3) Ω), (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3 ∧
      ∃ e : fixSubgroup Φ ≃* U, ∀ X : fixSubgroup Φ,
        (∃ c : Ω, ((X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ↔
          ∃ c : Ω, (((e X : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ∧
    CFSG.IsQuasisimple (fixSubgroup Φ) ∧
    (∀ X : fixSubgroup Φ, X ∈ Subgroup.center (fixSubgroup Φ) ↔
      ∃ c : Ω, ((X : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ∧
    Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd 3 (ℓ ^ f + 1) ∧
    ∃ J : SL(3, Ω), ∀ A : SL(2, RingHom.eqLocusField Fr (RingHom.id Ω)),
      J * (blockSL Ω 2 1 (SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype
        A) : SL(3, Ω)) * J⁻¹ ∈ fixSubgroup Φ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  have h₁ := natCard_eqLocusField_frob hℓ hf hFr
  have hq : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  set k₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id K)
  obtain ⟨-, ⟨H, hH⟩, ⟨J, hJ⟩, -, hbig⟩ := sl3_root_permuting_frobenius_fixed_unitary
    (k := k₀) hℓ hf h₀ π Φ b fun i j hij t => by rw [hΦ, hFr]
  obtain ⟨hQ, hcent, hcard, -⟩ := hbig hq2
  set hG := SpecialLinearGroup.toGL H with hhG
  set U : Subgroup (GL (Fin 3) Ω) := ((fixSubgroup Φ).map SpecialLinearGroup.toGL).map
    (MulAut.conj hG⁻¹).toMonoidHom with hU
  have hinj : Function.Injective (SpecialLinearGroup.toGL : SL(3, Ω) →* GL (Fin 3) Ω) :=
    fun X Y h => Subtype.ext (congrArg Units.val h)
  let e : fixSubgroup Φ ≃* U :=
    ((fixSubgroup Φ).equivMapOfInjective _ hinj).trans
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj hG⁻¹).injective)
  have he : ∀ X : fixSubgroup Φ, ((e X : U) : GL (Fin 3) Ω) =
      hG⁻¹ * SpecialLinearGroup.toGL (X : SL(3, Ω)) * hG := fun X => by
    change (MulAut.conj hG⁻¹) (SpecialLinearGroup.toGL (X : SL(3, Ω))) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨⟨U, ?_, e, fun X => ?_⟩, hQ, hcent, hcard, J, fun A => ?_⟩
  · ext Y
    simp only [SetLike.mem_coe, hU, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    constructor
    · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
      obtain ⟨Y', hY', hXY⟩ := (hH X).1 hX
      rw [hXY]
      simpa [hhG, mul_assoc] using hY'
    · intro hY
      have hdet : (Y : Matrix (Fin 3) (Fin 3) Ω).det = 1 := hY.2.1
      set Y₀ : SL(3, Ω) := ⟨Y, hdet⟩
      have hY₀ : SpecialLinearGroup.toGL Y₀ = Y := Units.ext rfl
      refine ⟨_, ⟨H * Y₀ * H⁻¹, (hH _).2 ⟨Y, hY, ?_⟩, rfl⟩, ?_⟩
      · rw [map_mul, map_mul, map_inv, hY₀]
      · rw [map_mul, map_mul, map_inv, hY₀, ← hhG]
        group
  · rw [he]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, hc]
      rw [← Matrix.scalar_commute c (fun r => Commute.all c r) ((hG⁻¹ : GL (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω)]
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have h1 : SpecialLinearGroup.toGL (X : SL(3, Ω)) = hG * (hG⁻¹ *
          SpecialLinearGroup.toGL (X : SL(3, Ω)) * hG) * hG⁻¹ := by group
      have h2 := congrArg Units.val h1
      rw [SpecialLinearGroup.coe_GL_coe_matrix] at h2
      rw [h2, Units.val_mul, Units.val_mul, hc,
        ← Matrix.scalar_commute c (fun r => Commute.all c r) ((hG : GL (Fin 3) Ω) :
          Matrix (Fin 3) (Fin 3) Ω), mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
  · have h := hJ (SpecialLinearGroup.map (threeSixFieldEquiv hσ hFr h₀ h₁ hq).symm.toRingHom A)
    rwa [map_algebraMap_eq hσ hFr h₀ h₁ hq] at h

end Fix

end CFSG.RankThree.Chevalley
