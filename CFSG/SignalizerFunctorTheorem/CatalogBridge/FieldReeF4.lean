module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
import CFSG.SignalizerFunctorTheorem.CatalogBridge.ReeStabilizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
import CFSG.RankThree.PartTwo.KFacts.KS14SzRee

public section

open CFSG.Open (signalizerFixedSubgroup signalizerNearPSolvable)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form
  large_Ree_model_field_outer_group_and_inner_involutions ringAut_commute)
open CFSG.RankThree.Chevalley (ringEquiv_eq_one_of_card_eq_prime)
open CFSG.RankThree.PartTwo.KFacts.KS14 (three_dvd_card_of_reeTitsModel_twistedF4)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem fieldClauses_largeRee
    {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpΓ : ¬ p ∣ Nat.card (ReeTag.F4.reeGamma K a))
    (hNL : SubfieldNonLocalizedLargeRee) : FieldClauses p (ReeTag.F4.reeGamma K a) := by
  classical
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : ∀ (x : ReeTag.F4.reeGamma K a) (β : K ≃+* K),
      Θ (MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a β) = β := fun x β => by
    rw [← hΨ x β]
    change SemidirectProduct.rightHom (Ψ.symm (Ψ ⟨x, β⟩)) = β
    rw [MulEquiv.symm_apply_apply]
    rfl
  rintro ⟨α, hα⟩
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  have hΘα : Θ α = σ := by
    rw [hxσ]
    exact hΘ x σ
  have hσp : σ ^ p = 1 := by
    rw [← hΘα, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  have hσ1 : σ ≠ 1 := by
    intro h
    have hαx : α = MulAut.conj x := by
      rw [hxσ]
      change MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a σ = _
      rw [h, hone, mul_one]
    have hd : orderOf α ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
      rw [hαx]
      exact (orderOf_map_dvd (MulAut.conj : ReeTag.F4.reeGamma K a →*
        MulAut (ReeTag.F4.reeGamma K a)) x).trans (orderOf_dvd_natCard x)
    rw [hα] at hd
    exact hpΓ hd
  have : Fact p.Prime := ⟨hp⟩
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hinj : Function.Injective (ReeTag.F4.reeGammaFieldAutHom K a) := fun s t h => by
    have h1 := hΘ 1 s
    have h2 := hΘ 1 t
    rw [map_one, one_mul] at h1 h2
    exact h1.symm.trans ((congrArg Θ h).trans h2)
  have hord : orderOf (ReeTag.F4.reeGammaFieldAut K a σ) = p := by
    have := orderOf_injective _ hinj σ
    rwa [hσ] at this
  obtain ⟨b, hkcard, hfixed⟩ := largeRee_fixed_data ha hK hp hp3 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinner : ∀ ρ : fixSubfield σ ≃+* fixSubfield σ,
      ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          (ReeTag.F4.reeGamma (fixSubfield σ) b) → ρ = 1 := by
    intro ρ hρ
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      exact ringEquiv_eq_one_of_card_eq_prime Nat.prime_two (by simpa using hkcard) ρ
    · obtain ⟨-, hNFk, -⟩ :=
        large_Ree_full_inner_field_automorphism_normal_form b hb1 (fixSubfield σ) hkcard
      obtain ⟨y, hy⟩ := hρ
      obtain ⟨q, -, huniq⟩ := hNFk (ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ)
      have hone' : ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b 1 = 1 :=
        map_one (ReeTag.F4.reeGammaFieldAutHom (fixSubfield σ) b)
      have h1 := huniq (1, ρ) (by simp)
      have h2 := huniq (y, 1) (by
        change ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b ρ =
          MulAut.conj y * ReeTag.F4.reeGammaFieldAut (fixSubfield σ) b 1
        rw [hone', mul_one]
        exact hy.symm)
      exact congrArg Prod.snd (h1.trans h2.symm)
  have hNLC := hNL a ha K hK p hp hp3 σ hσ
  have hC : Subgroup.centralizer
      (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) : Set (ReeTag.F4.reeGamma K a)) =
        ⊥ := centralizer_eq_bot_of_nonLocalized hNLC
  have hS : ∀ g : MulAut (ReeTag.F4.reeGamma K a),
      (∀ x ∈ signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ), g x = x) →
        g ∈ Subgroup.zpowers (ReeTag.F4.reeGammaFieldAut K a σ) := fun g hg =>
    mem_zpowers_of_fixes_of_normalForm (fun u v => ringAut_commute u v)
      (ReeTag.F4.reeGammaFieldAutHom K a)
      (fun β => by
        obtain ⟨⟨x, τ⟩, h, -⟩ := hNF β
        exact ⟨x, τ, h⟩) σ _ (fun _ => Iff.rfl) hC
      (fun x τ hx hfix => ree_zpowers_of_inner_on_subfield σ hfixed hinner x τ hx hfix) hg
  exact ⟨_, hord, fixedClauses_of_stabilizer hord (largeReeFixedSimple a ha K hK p hp hp3 σ hσ)
    (fun _ => hNLC) hS⟩

theorem fieldClauses_reeF4
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedF4 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedLargeRee) : FieldClauses p T := by
  have hp3 : 3 < p := by
    have h3 := three_dvd_card_of_reeTitsModel_twistedF4 hm
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  obtain ⟨rfl, hf3, -, -, -, -, hiso⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions T ℓ f hm
  obtain ⟨-, a, hfa, K, _, _, hK, hw⟩ := hm
  have : CharP K ReeTag.F4.prime :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨⟨E⟩, -⟩ := hiso a K hfa hK hw
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv T E.toEquiv
  have hpΓ : ¬ p ∣ Nat.card (ReeTag.F4.reeGamma K a) := by rwa [← Nat.card_congr E.toEquiv]
  exact FieldClauses.of_mulEquiv E.symm (fieldClauses_largeRee (by omega) K hK' hp hp3 hpΓ hNL)

theorem nearOrField_reeF4
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedF4 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedLargeRee) :
    signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_reeF4 hm hp hp2 hpT hNL)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
