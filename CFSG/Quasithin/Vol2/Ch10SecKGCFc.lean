module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFb
public import CFSG.Quasithin.Vol2.Ch10SecQ34MD
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut)
open scoped Matrix

variable {a : ℕ} {K : Type} [Field K]

theorem hasScalarCommutant_sz : HasScalarCommutant (suzukiGroup a K) := fun f hf =>
  C10P34.eq_smul_of_comm_suzuki a f (hf _ (C10P34.sElt a 1 0).2)
    (fun v => hf _ (C10P34.sElt a 0 v).2) (hf _ (C10P34.wElt a K).2)

theorem fieldMap_mul_natAut_sz (σ : K ≃+* K) (γ : suzukiGroup a K) :
    fieldMap σ * natAut (suzukiGroup a K) γ * (fieldMap σ)⁻¹ =
      natAut (suzukiGroup a K) (szFieldAut a K σ γ) :=
  toAddMap_injective fun v => by
    rw [toAddMap_natAut, coe_szFieldAut]
    exact toAddMap_fieldMap_conj σ (γ : GL (Fin 4) K) v

theorem fieldMap_mem_natNorm_sz (σ : K ≃+* K) : fieldMap σ ∈ natNorm (suzukiGroup a K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨szFieldAut a K σ γ, (fieldMap_mul_natAut_sz σ γ).symm⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨szFieldAut a K σ.symm γ, ?_⟩
    have h := fieldMap_mul_natAut_sz σ.symm γ
    rw [fieldMap_symm, inv_inv] at h
    rw [← h, hγ]
    group

theorem conjHom_fieldMap_sz (σ : K ≃+* K) :
    conjHom (suzukiGroup a K) ⟨fieldMap σ, fieldMap_mem_natNorm_sz σ⟩ = szFieldAut a K σ := by
  refine MulEquiv.ext fun γ => ?_
  apply natAut_injective
  rw [natAut_conjHom]
  exact fieldMap_mul_natAut_sz σ γ

theorem isSemilinear_of_smul_sz {g : MulAut (StdMod (Fin 4) K)} {c : K}
    {A : Matrix (Fin 4) (Fin 4) K} (h : ∀ v, toAddMap g v = c • (A *ᵥ v)) :
    IsSemilinear g (RingEquiv.refl K) := by
  intro l v
  rw [h, h, Matrix.mulVec_smul, smul_comm]
  rfl

theorem exists_smul_of_linear_sz (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : MulAut (StdMod (Fin 4) K)} (hg : g ∈ natNorm (suzukiGroup a K))
    (hlin : IsSemilinear g (RingEquiv.refl K)) :
    ∃ s : suzukiGroup a K, ∃ c : K, ∀ v, toAddMap g v =
      c • ((((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  obtain ⟨⟨s, σ⟩, hsσ⟩ := e.surjective (conjHom (suzukiGroup a K) ⟨g, hg⟩)
  rw [he] at hsσ
  let g' : ↥(natNorm (suzukiGroup a K)) := ⟨g, hg⟩ * ⟨fieldMap σ, fieldMap_mem_natNorm_sz σ⟩⁻¹
  have h2 : conjHom (suzukiGroup a K) g' = MulAut.conj s := by
    rw [map_mul, map_inv, conjHom_fieldMap_sz, ← hsσ, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := exists_smul_of_conjHom_eq hasScalarCommutant_sz g' s h2
  have hgg : g = (g' : MulAut (StdMod (Fin 4) K)) * fieldMap σ := by
    change g = g * (fieldMap σ)⁻¹ * fieldMap σ
    group
  have hσsl : IsSemilinear g (σ.trans (RingEquiv.refl K)) := by
    rw [hgg]
    exact (isSemilinear_of_smul_sz hc).mul (isSemilinear_fieldMap σ)
  have hσ1 : σ.trans (RingEquiv.refl K) = RingEquiv.refl K := hσsl.unique hlin
  have hσ2 : σ = 1 := by
    ext x
    exact congrArg (fun τ : K ≃+* K => τ x) hσ1
  refine ⟨s, c, fun v => ?_⟩
  have hg' : (g' : MulAut (StdMod (Fin 4) K)) = g := by
    have h1 : fieldMap (ι := Fin 4) (1 : RingAut K) = 1 := toAddMap_injective fun _ => rfl
    rw [hgg, hσ2, h1, mul_one]
  rw [← hg']
  exact hc v

theorem eq_one_of_pow_four_eq_one [CharP K 2] {c : K} (h : c ^ 4 = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ 2 = c ^ 2 ^ 2 - 1 ^ 2 ^ 2 := sub_pow_char_pow c 1 2
  have h2 : (c - 1) ^ 2 ^ 2 = 0 := by
    rw [h1, one_pow]
    norm_num [h]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)

theorem eq_one_natSz (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {V : Type}
    [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {π : ↥(suzukiGroup a K) →* ↥H}
    (hπ : Function.Surjective π) {e : V ≃* StdMod (Fin 4) K}
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = natAct (suzukiGroup a K) γ (e v))
    {r : ℕ} (hr : r.Prime) (hrH : ¬ r ∣ Nat.card H) {x : MulAut V}
    (hx : IsSemi (smOf e) x 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hxr : x ^ r = 1) : x = 1 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨s, c, hc⟩ := exists_smul_of_linear_sz ha hK (congrHom_mem_natNorm hπ he hxH)
    (isSemilinear_congrHom hx)
  set S : Matrix (Fin 4) (Fin 4) K :=
    (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hS
  have hpow : ∀ (k : ℕ) v, toAddMap (congrHom e x ^ k) v = c ^ k • ((S ^ k) *ᵥ v) := by
    intro k
    induction k with
    | zero => intro v; simp [toAddMap_one]
    | succ k ih =>
      intro v
      rw [pow_succ, toAddMap_mul, hc, ih, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec,
        ← pow_succ, ← pow_succ]
  have hyr : congrHom e x ^ r = 1 := by rw [← map_pow, hxr, map_one]
  have hM : (c ^ r) • (S ^ r) = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have h1 := hpow r v
    rw [hyr, toAddMap_one] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact h1.symm
  have hdet : (c ^ r) ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_pow, Fintype.card_fin, Matrix.det_one, hS,
      CFSG.LieType.Ree.det_suzukiGroup, one_pow, mul_one] at h1
    exact h1
  have hcr : c ^ r = 1 := eq_one_of_pow_four_eq_one hdet
  have hSr : S ^ r = 1 := by rwa [hcr, one_smul] at hM
  have hsr : s ^ r = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact hSr))
  have hcard : Nat.card H = Nat.card (suzukiGroup a K) := card_eq_of_natAct hπ he
  have hs1 : s = 1 := eq_one_of_pow_prime hr (by rwa [← hcard]) hsr
  have hc1 : c = 1 := by
    refine eq_one_of_pow_prime_of_dvd hr (N := Nat.card H) ?_ hrH hcr
    rw [hcard, CFSG.LieType.Ree.suzuki_order hK, hK]
    exact (dvd_mul_left _ _).mul_right _
  apply congrHom_injective e
  rw [map_one]
  refine toAddMap_injective fun v => ?_
  rw [hc, hc1, one_smul, hS, hs1]
  simp [toAddMap_one]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
