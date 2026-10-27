module

public import CFSG.Quasithin.Recognition.CertD4BridgeGen
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Open (quasithinRootElt quasithinD4Root quasithinTrialityD4Two quasithinTrialityGens)

section Center

variable {k : Type} [Field k]

theorem d4b_poly_zero [Finite k] (hk : Nat.card k = 8) (c₁ c₂ c₄ c₆ : k)
    (h : ∀ a : k, c₁ * a + c₂ * a ^ 2 + c₄ * a ^ 4 + c₆ * a ^ 6 = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₄ = 0 ∧ c₆ = 0 := by
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 8 := by rw [← Nat.card_eq_fintype_card]; exact hk
  open Polynomial in
  let p : k[X] := C c₁ * X + C c₂ * X ^ 2 + C c₄ * X ^ 4 + C c₆ * X ^ 6
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := id)
      Function.injective_id (fun a => by simpa [p] using h a) ?_
    rw [hcard]
    simp only [p]
    compute_degree!
  have h1 : p.coeff 1 = c₁ := by simp [p, Polynomial.coeff_C_mul]
  have h2 : p.coeff 2 = c₂ := by simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]
  have h4 : p.coeff 4 = c₄ := by simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]
  have h6 : p.coeff 6 = c₆ := by simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]
  rw [hp] at h1 h2 h4 h6
  simp only [Polynomial.coeff_zero] at h1 h2 h4 h6
  exact ⟨h1.symm, h2.symm, h4.symm, h6.symm⟩


variable [CharP k 2]

theorem d4bEs_zero_one : ∀ s : Bool,
    d4bEs ⟨0, by decide⟩ s * d4bEs ⟨1, by decide⟩ s = 0 := by decide +kernel

theorem d4bEs_zero_three : ∀ s : Bool,
    d4bEs ⟨0, by decide⟩ s * d4bEs ⟨3, by decide⟩ s = 0 := by decide +kernel

theorem d4b_twist_expand (s : Bool) (a : k) :
    d4bUm k ⟨0, by decide⟩ s a * d4bUm k ⟨1, by decide⟩ s (a ^ 2) *
        d4bUm k ⟨3, by decide⟩ s (a ^ 4) =
      1 + a • d4bEk k ⟨0, by decide⟩ s + a ^ 2 • d4bEk k ⟨1, by decide⟩ s +
        a ^ 4 • d4bEk k ⟨3, by decide⟩ s +
        a ^ 6 • (d4bEk k ⟨1, by decide⟩ s * d4bEk k ⟨3, by decide⟩ s) := by
  have h01 : d4bEk k ⟨0, by decide⟩ s * d4bEk k ⟨1, by decide⟩ s = 0 := by
    rw [d4bEk, d4bEk, ← map_mul, d4bEs_zero_one, map_zero]
  have h03 : d4bEk k ⟨0, by decide⟩ s * d4bEk k ⟨3, by decide⟩ s = 0 := by
    rw [d4bEk, d4bEk, ← map_mul, d4bEs_zero_three, map_zero]
  unfold d4bUm
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul, h01, h03, smul_zero, add_zero]
  module

theorem d4bG8_le_Ω : d4bG8 k ≤ d4bΩ k := by
  rw [d4bG8, Subgroup.closure_le]
  rintro A (⟨a, s, hA⟩ | ⟨s, hA⟩)
  · have : A = d4bNat k ⟨0, by decide⟩ s a * d4bNat k ⟨1, by decide⟩ s (a ^ 2) *
        d4bNat k ⟨3, by decide⟩ s (a ^ 4) := by
      apply Units.ext
      rw [hA, Units.val_mul, Units.val_mul]
      exact (d4bUm_outer ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ rfl rfl rfl s a _ _).symm
    rw [SetLike.mem_coe, this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (d4bNat_mem k _ s a) (d4bNat_mem k _ s _))
      (d4bNat_mem k _ s _)
  · have : A = d4bNat k ⟨2, by decide⟩ s 1 := by
      apply Units.ext
      rw [hA]
      exact (d4bUm_mid ⟨2, by decide⟩ rfl s 1).symm
    rw [SetLike.mem_coe, this]
    exact d4bNat_mem k _ s 1

theorem d4b_outer_mem_gens (s : Bool) (a : k) :
    ((d4bNat k ⟨0, by decide⟩ s a * d4bNat k ⟨1, by decide⟩ s (a ^ 2) *
      d4bNat k ⟨3, by decide⟩ s (a ^ 4) : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) ∈
      d4bTwGens k := by
  refine Or.inl ⟨a, s, ?_⟩
  rw [Units.val_mul, Units.val_mul]
  exact d4bUm_outer ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ rfl rfl rfl s a _ _

omit [CharP k 2] in
theorem d4b_comm_of_poly [Finite k] (hk : Nat.card k = 8)
    (zm E0 E1 E3 F : Matrix (Fin 8) (Fin 8) k)
    (h : ∀ a : k, zm * (1 + a • E0 + a ^ 2 • E1 + a ^ 4 • E3 + a ^ 6 • F) =
      (1 + a • E0 + a ^ 2 • E1 + a ^ 4 • E3 + a ^ 6 • F) * zm) :
    zm * E0 = E0 * zm ∧ zm * E1 = E1 * zm ∧ zm * E3 = E3 * zm := by
  have hentry : ∀ r c : Fin 8, (zm * E0 - E0 * zm) r c = 0 ∧ (zm * E1 - E1 * zm) r c = 0 ∧
      (zm * E3 - E3 * zm) r c = 0 ∧ (zm * F - F * zm) r c = 0 := by
    intro r c
    refine d4b_poly_zero hk _ _ _ _ (fun a => ?_)
    have := congrFun (congrFun (h a) r) c
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
    linear_combination this
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.1 (Matrix.ext fun r c => (hentry r c).1)
  · exact sub_eq_zero.1 (Matrix.ext fun r c => (hentry r c).2.1)
  · exact sub_eq_zero.1 (Matrix.ext fun r c => (hentry r c).2.2.1)


theorem d4b_twist_expand_nat (s : Bool) (a : k) :
    ((d4bNat k ⟨0, by decide⟩ s a * d4bNat k ⟨1, by decide⟩ s (a ^ 2) *
        d4bNat k ⟨3, by decide⟩ s (a ^ 4) : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) =
      1 + a • d4bEk k ⟨0, by decide⟩ s + a ^ 2 • d4bEk k ⟨1, by decide⟩ s +
        a ^ 4 • d4bEk k ⟨3, by decide⟩ s +
        a ^ 6 • (d4bEk k ⟨1, by decide⟩ s * d4bEk k ⟨3, by decide⟩ s) := by
  rw [Units.val_mul, Units.val_mul]
  exact d4b_twist_expand s a

theorem d4b_center_comm
    [Finite k] (hk : Nat.card k = 8) (z : ↥(d4bG8 k))
    (hz : z ∈ Subgroup.center ↥(d4bG8 k)) (i : Fin Tag.D4.rank) (s : Bool) :
    ((z : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * d4bEk k i s =
      d4bEk k i s * ((z : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) := by
  set zm : Matrix (Fin 8) (Fin 8) k := ((z : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) with hzm
  have hcen : ∀ A : GL (Fin 8) k, (A : Matrix (Fin 8) (Fin 8) k) ∈ d4bTwGens k →
      zm * (A : Matrix (Fin 8) (Fin 8) k) = (A : Matrix (Fin 8) (Fin 8) k) * zm := by
    intro A hA
    have h := Subgroup.mem_center_iff.1 hz ⟨A, Subgroup.subset_closure hA⟩
    have h' := congrArg (fun g : ↥(d4bG8 k) => ((g : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)) h
    simpa [hzm] using h'.symm
  have hout : ∀ s : Bool,
      zm * d4bEk k ⟨0, by decide⟩ s = d4bEk k ⟨0, by decide⟩ s * zm ∧
      zm * d4bEk k ⟨1, by decide⟩ s = d4bEk k ⟨1, by decide⟩ s * zm ∧
      zm * d4bEk k ⟨3, by decide⟩ s = d4bEk k ⟨3, by decide⟩ s * zm := by
    intro s
    refine d4b_comm_of_poly hk zm _ _ _ (d4bEk k ⟨1, by decide⟩ s * d4bEk k ⟨3, by decide⟩ s)
      (fun a => ?_)
    have hA := hcen _ (d4b_outer_mem_gens s a)
    rwa [d4b_twist_expand_nat] at hA
  have hmid : ∀ s : Bool, zm * d4bEk k ⟨2, by decide⟩ s = d4bEk k ⟨2, by decide⟩ s * zm := by
    intro s
    have hA := hcen (d4bNat k ⟨2, by decide⟩ s 1) (Or.inr ⟨s, d4bUm_mid ⟨2, by decide⟩ rfl s 1⟩)
    change zm * d4bUm k ⟨2, by decide⟩ s 1 = d4bUm k ⟨2, by decide⟩ s 1 * zm at hA
    unfold d4bUm at hA
    simpa [mul_add, add_mul] using hA
  match i with
  | ⟨0, _⟩ => exact (hout s).1
  | ⟨1, _⟩ => exact (hout s).2.1
  | ⟨2, _⟩ => exact hmid s
  | ⟨3, _⟩ => exact (hout s).2.2

theorem d4b_center_G8
    [Finite k] (hk : Nat.card k = 8) : Subgroup.center ↥(d4bG8 k) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨c, hc⟩ := d4b_scalar k ((z : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)
    (fun i s => d4b_center_comm hk z hz i s)
  have hdet := d4b_det_Ω k (z : GL (Fin 8) k) (d4bG8_le_Ω z.2)
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 8 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hc1 : c = 1 := by
    have h8 : c ^ 8 = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [← h8]
    exact hdet
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Units.ext (by rw [hc, hc1, one_smul]; rfl))

end Center

section Equiv

variable {k : Type} [Field k] [CharP k 2] [Finite k] (hk : Nat.card k = 8) (σ : k →+* k)
  (hσ : ∀ c, σ c = c ^ 2)

include hσ in
@[expose] noncomputable def d4bΓ
    : twistedGroup σ →* d4bG8 k :=
  ((d4bΨ' hk).comp (twistedGroup σ).subtype).codRestrict (d4bG8 k)
    (fun x => d4b_twistedGroup_le hk σ hσ x.2)

include hσ in
theorem d4bΓ_surjective
    : Function.Surjective (d4bΓ hk σ hσ) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (d4b_G8_le_map hk σ hσ hy)
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

include hσ in
theorem d4bΓ_apply
    (x : twistedGroup σ) :
    ((d4bΓ hk σ hσ x : d4bG8 k) : GL (Fin 8) k) = d4bΨ' hk (x : adjointGroup d4 k) := rfl

include hσ in
theorem d4bΓ_nontrivial
    : ∃ x, d4bΓ hk σ hσ x ≠ 1 := by
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  refine ⟨⟨xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1,
    twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hp (ng 0))
      (xPar_two_mem σ hp (map_one σ))⟩, ?_⟩
  intro h
  have h1 : d4bΨ' hk (xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1) = 1 := by
    have := congrArg (fun y : ↥(d4bG8 k) => (y : GL (Fin 8) k)) h
    exact this
  rw [one_smul, d4bΨ_xPar_pos hk] at h1
  have h2 := congrArg (fun y : GL (Fin 8) k => (y : Matrix (Fin 8) (Fin 8) k) 1 2) h1
  change d4bUm k (nd 2) true 1 1 2 = (1 : Matrix (Fin 8) (Fin 8) k) 1 2 at h2
  rw [d4bUm_mid (nd 2) rfl true 1] at h2
  simp [quasithinRootElt, quasithinD4Root] at h2

include hσ in
noncomputable def d4bQuotEquiv
    (hq : IsQuasisimple (twistedGroup σ)) :
    twistedGroup σ ⧸ Subgroup.center (twistedGroup σ) ≃* d4bG8 k :=
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
    (φ := d4bΓ hk σ hσ) (d4bΓ_nontrivial hk σ hσ)
  (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq (d4bΓ_surjective hk σ hσ)
    hker).trans
    ((QuotientGroup.quotientMulEquivOfEq (d4b_center_G8 hk)).trans QuotientGroup.quotientBot)

end Equiv

section Transport

private theorem d4b_map_rootElt {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (pos : List (Fin 8 × Fin 8)) (t : K) :
    (quasithinRootElt pos t).map f = quasithinRootElt pos (f t) := by
  ext r c
  simp only [quasithinRootElt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

private theorem d4b_map_rootProd {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a : K)
    (s : Bool) :
    (quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)).map f =
    quasithinRootElt (quasithinD4Root 0 s) (f a) *
      quasithinRootElt (quasithinD4Root 2 s) (f a ^ 2) *
      quasithinRootElt (quasithinD4Root 3 s) (f a ^ 4) := by
  rw [Matrix.map_mul, Matrix.map_mul, d4b_map_rootElt, d4b_map_rootElt, d4b_map_rootElt,
    map_pow, map_pow]

private theorem d4b_coe_map_gl {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (A : GL (Fin 8) K) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) =
      (A : Matrix (Fin 8) (Fin 8) K).map f := by
  simp [Matrix.GeneralLinearGroup.map]

theorem d4bG8_equiv_quasithin (k : Type) [Field k] [Finite k] (hk : Nat.card k = 8) :
    Nonempty (d4bG8 k ≃* quasithinTrialityD4Two) := by
  have : Fintype k := Fintype.ofFinite k
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have e : k ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk,
      GaloisField.card 2 3 (by norm_num)]
    norm_num)
  let ψ : GL (Fin 8) k →* GL (Fin 8) (GaloisField 2 3) :=
    Matrix.GeneralLinearGroup.map e.toRingHom
  have hinj : Function.Injective ψ := by
    refine Units.map_injective (f := (e.toRingHom.mapMatrix : Matrix (Fin 8) (Fin 8) k →+*
      Matrix (Fin 8) (Fin 8) (GaloisField 2 3)).toMonoidHom) ?_
    intro M N h
    exact Matrix.map_injective e.injective h
  have hset : ψ '' {A : GL (Fin 8) k | (A : Matrix (Fin 8) (Fin 8) k) ∈ d4bTwGens k} =
      {A : GL (Fin 8) (GaloisField 2 3) |
        (A : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) ∈ quasithinTrialityGens} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      rcases hA with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨e a, s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map e.toRingHom A : GL (Fin 8) (GaloisField 2 3)) :
          Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) = _
        rw [d4b_coe_map_gl, hs, d4b_map_rootProd]
        rfl
      · refine Or.inr ⟨s, ?_⟩
        show ((Matrix.GeneralLinearGroup.map e.toRingHom A : GL (Fin 8) (GaloisField 2 3)) :
          Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) = _
        rw [d4b_coe_map_gl, hs, d4b_map_rootElt, map_one]
    · intro hB
      let A : GL (Fin 8) k := Matrix.GeneralLinearGroup.map e.symm.toRingHom B
      have hA : (A : Matrix (Fin 8) (Fin 8) k) =
          (B : Matrix (Fin 8) (Fin 8) (GaloisField 2 3)).map e.symm := d4b_coe_map_gl _ B
      have hψA : ψ A = B := by
        apply Units.ext
        show ((Matrix.GeneralLinearGroup.map e.toRingHom A : GL (Fin 8) (GaloisField 2 3)) :
          Matrix (Fin 8) (Fin 8) (GaloisField 2 3)) = _
        rw [d4b_coe_map_gl, hA, Matrix.map_map]
        ext i j
        simp
      refine ⟨A, ?_, hψA⟩
      rcases hB with ⟨a, s, hs⟩ | ⟨s, hs⟩
      · refine Or.inl ⟨e.symm a, s, ?_⟩
        rw [hA, hs]
        exact d4b_map_rootProd e.symm.toRingHom a s
      · refine Or.inr ⟨s, ?_⟩
        rw [hA, hs]
        show (quasithinRootElt (quasithinD4Root 1 s) (1 : GaloisField 2 3)).map e.symm.toRingHom = _
        rw [d4b_map_rootElt, map_one]
  have hmap : (d4bG8 k).map ψ = quasithinTrialityD4Two := by
    rw [d4bG8, quasithinTrialityD4Two, MonoidHom.map_closure, hset]
  exact ⟨(Subgroup.equivMapOfInjective _ ψ hinj).trans (MulEquiv.subgroupCongr hmap)⟩

end Transport

theorem trialityD4ModelBridge_of_lieModel
    (X : Type) [Group X]
    (h : LieModel X .trialityD4 0 2 1) : Nonempty (X ≃* quasithinTrialityD4Two) := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, hX⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hX
    have hK3 : Nat.card K = 2 ^ 3 := hK
    have hK8 : Nat.card K = 8 := by rw [hK3]; norm_num
    have hσ' : ∀ c, σ c = c ^ 2 := fun c => by simpa using hσ c
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 3) (by
      rw [← Nat.card_eq_fintype_card, hK8]; norm_num)
    have hq : IsQuasisimple (twistedGroup σ) :=
      twistedGroup_isQuasisimple_of_card (q := 2) (by norm_num) hK3 hσ'
    let eΓ := twistedGroupEquivDerived σ (q := 2) (by norm_num) hK3 hσ'
    let eQ := QuotientGroup.congr (Subgroup.center (twistedGroup σ)) _ eΓ
      (Subgroup.map_center_eq eΓ)
    obtain ⟨eG⟩ := d4bG8_equiv_quasithin K hK8
    exact ⟨e.trans (eQ.symm.trans ((d4bQuotEquiv hK8 σ hσ' hq).trans eG))⟩
  · exact absurd hree (by decide)
  · exact absurd hsz (by decide)

end CFSG.Quasithin
