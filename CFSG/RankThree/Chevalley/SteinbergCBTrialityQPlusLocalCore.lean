module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusTransport

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2 TrialitySplitInner
open Subgroup
open scoped Pointwise commutatorElement

theorem map_centralizer_singleton_of_injective {C G : Type*} [Group C] [Group G] {F : C →* G}
    (hF : Function.Injective F) {Γ : Subgroup G} (hrange : F.range = Γ) (x : C) :
    (centralizer ({x} : Set C)).map F = Γ ⊓ centralizer {F x} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hrange ▸ ⟨y, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy]
  · intro hz
    obtain ⟨hzΓ, hzc⟩ := Subgroup.mem_inf.1 hz
    rw [← hrange] at hzΓ
    obtain ⟨y, rfl⟩ := hzΓ
    refine ⟨y, mem_centralizer_singleton_iff.2 (hF ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 hzc

section Realization

variable {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K K₂ : Type} [Field K] [Field K₂]
  [Algebra K K₂] (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) {σ : K ≃+* K}
  (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {σ₂ : K₂ ≃+* K₂} (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
  {τ : K₂ ≃+* K₂} (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3))

include hℓ hf hK hK₂ hσ hσ₂ hτ in
theorem exists_realization_le_torus
    {g : ModGL TwistTag.D4.tag K₂}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom)
    (hzg : trialityOpposition K₂ = g * (Units.map (entrywiseHom τ.toRingHom) g)⁻¹)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f + 1)
    {P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hP : IsPGroup p P) :
    ∃ u ∈ trialityConjImage K σ.toRingHom g,
      (trialityRealization (σ := σ) (u * g)).range = trialityConjImage K σ.toRingHom g ∧
      ∀ c ∈ P, trialityRealization (σ := σ) (u * g) c ∈
        graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ.toRingHom g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, -, -, -, -, hsyl⟩ := hall g hg hzg
  obtain ⟨⟨S₀, hS₀⟩, -⟩ := hsyl p hp hp3 hpq
  set Γ := trialityConjImage K σ.toRingHom g with hΓdef
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (ModGL TwistTag.D4.tag K₂) := finite_modGL
  have hmemΓ : ∀ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      trialityRealization (σ := σ) g c ∈ Γ := fun c => ⟨c, c.2, rfl⟩
  set ιG : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* Γ :=
    (trialityRealization (σ := σ) g).codRestrict Γ hmemΓ
  obtain ⟨u, hu⟩ := exists_map_conj_le_of_sylow_le hS₀ (hP.map ιG)
  have hrange_g : (trialityRealization (σ := σ) g).range = Γ := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact hmemΓ c
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hreal : ∀ c, trialityRealization (σ := σ) ((u : ModGL TwistTag.D4.tag K₂) * g) c =
      (u : ModGL TwistTag.D4.tag K₂) * trialityRealization (σ := σ) g c *
        (u : ModGL TwistTag.D4.tag K₂)⁻¹ := fun c => by
    rw [trialityRealization_apply, trialityRealization_apply]
    group
  refine ⟨u, u.2, ?_, fun c hc => ?_⟩
  · ext y
    constructor
    · rintro ⟨c, rfl⟩
      rw [hreal]
      exact mul_mem (mul_mem u.2 (hmemΓ c)) (inv_mem u.2)
    · intro hy
      have hy' : (u : ModGL TwistTag.D4.tag K₂)⁻¹ * y * u ∈ Γ :=
        mul_mem (mul_mem (inv_mem u.2) hy) u.2
      rw [← hrange_g] at hy'
      obtain ⟨c, hc⟩ := hy'
      refine ⟨c, ?_⟩
      rw [hreal, hc]
      group
  · have h1 : (MulAut.conj u).toMonoidHom (ιG c) ∈
        (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ Γ).subgroupOf Γ :=
      hu ⟨ιG c, ⟨c, hc, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf] at h1
    rw [hreal]
    exact h1

end Realization

theorem exists_qplus_setting
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Algebra K K₂) (σ₂ τ : K₂ ≃+* K₂)
      (g : ModGL TwistTag.D4.tag K₂),
      Nat.card K₂ = (ℓ ^ f) ^ 6 ∧ (∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4)) ∧
      (∀ c, τ c = c ^ ((ℓ ^ f) ^ 3)) ∧ g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ∧
      trialityOpposition K₂ = g * (Units.map (entrywiseHom τ.toRingHom) g)⁻¹ := by
  obtain ⟨K₂, _, _, hK₂⟩ := exists_qplus_extension hℓ hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have : CharP K₂ ℓ := charP_of_injective_algebraMap (algebraMap K K₂).injective ℓ
  obtain ⟨σ₂, hσ₂'⟩ := exists_frobenius_pow (L := K₂) (ℓ := ℓ) (f * 4)
  obtain ⟨τ, hτ'⟩ := exists_frobenius_pow (L := K₂) (ℓ := ℓ) (f * 3)
  have hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4) := fun c => by rw [hσ₂', pow_mul]
  have hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3) := fun c => by rw [hτ', pow_mul]
  obtain ⟨-, -, ⟨g, hg, hzg⟩, -⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ
    hf K K₂ hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ.toRingHom hτ
  exact ⟨K₂, inferInstance, inferInstance, σ₂, τ, g, hK₂, hσ₂, hτ, hg, hzg⟩

end CFSG.RankThree.Chevalley
