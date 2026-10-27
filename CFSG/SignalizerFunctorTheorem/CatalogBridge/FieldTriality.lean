module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree

public section

open CFSG.Open (signalizerFixedSubgroup signalizerNearPSolvable)
open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  finite_field_automorphism_fixed_field_cardinality)
open CFSG.RankThree.Chevalley (exists_mulEquiv_graphFixedRootGroup_of_twisted_prime
  triality_canonical_field_full_centralizer_and_pointwise_kernel
  Chevalley_exceptional_models_order_divisible_by_three)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem triality_normalForm_data
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      Nat.card (K ≃+* K) = 3 * f ∧
      Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -, -, hDC⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨Θ, hker, hcard, hDC⟩
  · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -, -, hDC⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ
    exact ⟨Θ, hker, hcard, hDC⟩

theorem fieldClauses_triality
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp3 : 3 < p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hpC : ¬ p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hNL : SubfieldNonLocalizedTriality) :
    FieldClauses p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Θ, hΘker, hcard, -⟩ := triality_normalForm_data hℓ hf K hK σ hσ
  rintro ⟨α, hα⟩
  have hφp : Θ α ^ p = 1 := by rw [← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hφ1 : Θ α ≠ 1 := by
    intro h
    have hmem : α ∈ Θ.ker := h
    rw [hΘker] at hmem
    exact not_mem_inner_range_of_orderOf hpC hα hmem
  have hφord : orderOf (Θ α) = p := orderOf_eq_prime hφp hφ1
  have hpdvd : p ∣ 3 * f := by rw [← hcard, ← hφord]; exact orderOf_dvd_natCard _
  have hp3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨d, hd⟩ := Nat.Coprime.dvd_of_dvd_mul_left hp3' hpdvd
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  obtain ⟨φ, hφ, -, -, -, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δ, hδ⟩ : ∃ δ : K ≃+* K, ∀ c, δ c = c ^ ℓ ^ (3 * d) :=
    ⟨φ ^ (3 * d), fun c => ringAut_pow_apply_of_frobenius hφ (3 * d) c⟩
  have hK' : Nat.card K = ℓ ^ (3 * d * p) := by
    rw [hK3, hd]
    ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by
    rw [hσ, show d * p = f by rw [hd]; ring]
  obtain ⟨hord, -, -, -, -, -, hmap, hsimple, hnc, -, -, -, -, hcent, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd1 hp.two_le hp3' K hK' σ
      hσ' δ hδ
  set δ₀ := fieldActor σ δ with hδ₀
  have hFix : signalizerFixedSubgroup δ₀ = δ₀.toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eNJ : signalizerFixedSubgroup δ₀ ≃* trialityFieldImage σ δ :=
    ((signalizerFixedSubgroup δ₀).equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hmap))
  have hs : IsSimpleGroup (signalizerFixedSubgroup δ₀) := eNJ.isSimpleGroup
  have hn : ∃ a b : signalizerFixedSubgroup δ₀, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro a b
    have h := hcon (eNJ.symm a) (eNJ.symm b)
    apply eNJ.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hJle : (trialityFieldImage σ δ).subgroupOf C ≤ signalizerFixedSubgroup δ₀ := by
    intro j hj
    have hj' : (j : ModGL TwistTag.D4.tag K) ∈ (δ₀.toMonoidHom.eqLocus (MonoidHom.id _)).map
        C.subtype := by
      rw [hmap]
      exact Subgroup.mem_subgroupOf.1 hj
    obtain ⟨x, hx, hxj⟩ := hj'
    have : x = j := Subtype.ext hxj
    subst this
    rw [hFix]
    exact hx
  have hM : ∀ m ∈ trialityFieldInner σ δ, ∃ x ∈ signalizerFixedSubgroup δ₀, MulAut.conj x = m := by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : (j : ModGL TwistTag.D4.tag K) ∈ (δ₀.toMonoidHom.eqLocus (MonoidHom.id _)).map
        C.subtype := by
      rw [hmap]
      exact Subgroup.mem_subgroupOf.1 hj
    obtain ⟨x, hx, hxj⟩ := hj'
    have : x = j := Subtype.ext hxj
    subst this
    exact ⟨x, by rw [hFix]; exact hx, rfl⟩
  have hOut : ∀ a b : MulAut C, ⁅a, b⁆ ∈ (MulAut.conj : C →* MulAut C).range :=
    fun a b => commutator_mem_inner_of_hom (fun x y => ringAut_commute x y) Θ hΘker a b
  exact ⟨δ₀, hord, fixedClauses_of_simple_fixed_S2 hord hs hn hOut
    (hS2_of_centralizer_inf_eq_of_conj_mem δ₀ (signalizerFixedSubgroup δ₀) _ hM hcent)
    fun _ => NonLocalized.mono hJle (hNL ℓ d p hℓ hd1 hp hp3 K hK' σ δ hσ' hδ)⟩

theorem fieldClauses_chevalleyTrialityD4
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .trialityD4 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedTriality) :
    FieldClauses p T := by
  have hp3 : 3 < p := by
    have h3 := Chevalley_exceptional_models_order_divisible_by_three T .trialityD4 ℓ f hm
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm.1 hadm.2.1 hmod
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  set σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij with hσdef
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ₀
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  let e' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* T := e
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv T e'.symm.toEquiv
  have hpC : ¬ p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rwa [Nat.card_congr e'.toEquiv]
  exact FieldClauses.of_mulEquiv e'
    (fieldClauses_triality hadm.1 hadm.2.1 hp hp3 K hK3 σ hσ hpC hNL)

theorem nearOrField_chevalleyTrialityD4
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .trialityD4 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedTriality) :
    signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_chevalleyTrialityD4 hm hp hp2 hpT hNL)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
