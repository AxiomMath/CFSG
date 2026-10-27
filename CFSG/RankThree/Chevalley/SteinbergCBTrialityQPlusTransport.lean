module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusCentralizers
public import CFSG.RankThree.Chevalley.SteinbergBLTrialitySplitInner
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import Mathlib.FieldTheory.Finite.Extension
public import Certificates.Certificate45
public import Certificates.Certificate52
public import Certificates.Certificate113
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2

theorem exists_map_conj_le_of_sylow_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T : Subgroup G} {S₀ : Sylow p G} (hS₀ : (S₀ : Subgroup G) ≤ T) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ u : G, P.map (MulAut.conj u).toMonoidHom ≤ T := by
  obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G S₁ S₀
  refine ⟨u, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hS₀
  rw [← hu, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS₁ hx)

theorem exists_qplus_extension {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Algebra K K₂), Nat.card K₂ = (ℓ ^ f) ^ 6 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  refine ⟨FiniteField.Extension K ℓ 2, inferInstance, inferInstance, ?_⟩
  rw [FiniteField.natCard_extension, hK, ← pow_mul]

theorem exists_frobenius_pow {L : Type} [Field L] [Finite L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (j : ℕ) : ∃ δ : L ≃+* L, ∀ c, δ c = c ^ (ℓ ^ j) :=
  ⟨RingEquiv.ofBijective (iterateFrobenius L ℓ j)
      ⟨(iterateFrobenius L ℓ j).injective,
        Finite.surjective_of_injective (iterateFrobenius L ℓ j).injective⟩,
    fun c => iterateFrobenius_def ℓ j c⟩

theorem exists_eq_frobenius_pow {L : Type} [Field L] [Finite L] {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hm : 1 ≤ m) (hL : Nat.card L = ℓ ^ m) (δ : L ≃+* L) : ∃ j : ℕ, ∀ c, δ c = c ^ (ℓ ^ j) := by
  obtain ⟨φ, hφ, hord, hφtop, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hm hL
  have hδ : δ ∈ Subgroup.zpowers φ := by rw [hφtop]; exact Subgroup.mem_top δ
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hδ)
  have hpow : ∀ (n : ℕ) (c : L), (φ ^ n) c = c ^ (ℓ ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]
  exact ⟨j, fun c => by rw [← hj, hpow]⟩

section Realization

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂] {σ : K ≃+* K}

@[expose] def trialityRealization
    (w : ModGL TwistTag.D4.tag K₂) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag K₂ :=
  (MulAut.conj w).toMonoidHom.comp
    ((baseChangeGL (algebraMap K K₂)).comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)

theorem trialityRealization_apply
    (w : ModGL TwistTag.D4.tag K₂)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    trialityRealization (σ := σ) w c = w * baseChangeGL (algebraMap K K₂) c * w⁻¹ :=
  rfl

theorem trialityRealization_injective
    (w : ModGL TwistTag.D4.tag K₂) :
    Function.Injective (trialityRealization (σ := σ) w) :=
  (MulAut.conj w).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)

theorem map_fieldActor_conj_eq
    [Finite K] (w : ModGL TwistTag.D4.tag K₂)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K) (δ₂ : K₂ ≃+* K₂)
    (hδ : ∀ k, δ₂ (algebraMap K K₂ k) = algebraMap K K₂ (δ k))
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    trialityRealization (σ := σ) w ((MulAut.conj y * fieldActor (t := TwistTag.D4) σ δ :
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) c) =
      (trialityRealization w y * w * (Units.map (entrywiseHom δ₂.toRingHom) w)⁻¹) *
        Units.map (entrywiseHom δ₂.toRingHom) (trialityRealization (σ := σ) w c) *
        (trialityRealization w y * w * (Units.map (entrywiseHom δ₂.toRingHom) w)⁻¹)⁻¹ := by
  have hcomp : (algebraMap K K₂).comp δ.toRingHom = δ₂.toRingHom.comp (algebraMap K K₂) :=
    RingHom.ext fun k => (hδ k).symm
  have hfield : baseChangeGL (algebraMap K K₂)
      ((fieldActor σ δ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) =
      Units.map (entrywiseHom δ₂.toRingHom) (baseChangeGL (algebraMap K K₂) c) := by
    rw [coe_fieldActor, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      baseChangeGL_baseChangeGL, hcomp]
  have hιc : baseChangeGL (algebraMap K K₂) (c : ModGL TwistTag.D4.tag K) =
      w⁻¹ * trialityRealization (σ := σ) w c * w := by
    rw [trialityRealization_apply]
    group
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, trialityRealization_apply w
    (fieldActor σ δ c), hfield, hιc, map_mul, map_mul, map_inv]
  group

end Realization

section TorusSemilinear

variable {t : TwistTag} {L : Type} [Field L] {σ : L →+* L}

theorem units_map_entrywiseHom_orbitConjRankOneHom
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) (w : WeylGroup t.tag) (b : Fin t.foldedTag.rank)
    (A : SL2 (orbitField t L σ b)) :
    Units.map (entrywiseHom τ.toRingHom) (orbitConjRankOneHom t L σ w b A) =
      orbitConjRankOneHom t L σ w b
        (Matrix.SpecialLinearGroup.map (orbitFieldRestrict τ hτ b : orbitField t L σ b →+*
          orbitField t L σ b) A) := by
  have h : (Units.map (entrywiseHom τ.toRingHom)).comp (orbitConjRankOneHom t L σ w b) =
      (orbitConjRankOneHom t L σ w b).comp (Matrix.SpecialLinearGroup.map
        (orbitFieldRestrict τ hτ b : orbitField t L σ b →+* orbitField t L σ b)) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Upper]
        exact units_map_entrywiseHom_orbitConjRankOneHom_uSL hτ w b c
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Lower]
        exact units_map_entrywiseHom_orbitConjRankOneHom_vSL hτ w b c
  exact congrArg (fun φ => φ A) h

theorem exists_semilinearConj_orbitConjRankOneHom_of_torus
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) {h : ModGL t.tag L} (hh : h ∈ graphFixedTorus t L σ)
    {w : WeylGroup t.tag} (hwρ : w ∈ relWeylTwist t) (b : Fin t.foldedTag.rank) :
    ∃ M : GL (Fin 2) (orbitField t L σ b), ∀ A,
      orbitConjRankOneHom t L σ w b (semilinearConj M (orbitFieldRestrict τ hτ b) A) =
        twistedEntrywise h τ.toRingHom (orbitConjRankOneHom t L σ w b A) := by
  obtain ⟨l, hl⟩ := exists_conj_orbitConjRankOneHom_eq_conjSL hh hwρ b
  refine ⟨diagUnitOne l, fun A => ?_⟩
  rw [twistedEntrywise_apply, units_map_entrywiseHom_orbitConjRankOneHom hτ, hl]
  rfl

end TorusSemilinear

end CFSG.RankThree.Chevalley
