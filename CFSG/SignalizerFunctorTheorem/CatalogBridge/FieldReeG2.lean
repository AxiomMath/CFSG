module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
import CFSG.SignalizerFunctorTheorem.CatalogBridge.ReeStabilizer
import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.RankThree.PartTwo.KFacts.KS14SzRee

public section

open CFSG.Open (signalizerFixedSubgroup signalizerNearPSolvable)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.ComponentClassification (OuterAutomorphisms.inner)
open CFSG.ComponentClassification.CatalogueBSmallRee (small_Ree_whole_group_p_components
  reeGamma_G2_simple)
open CFSG.LieType.Ree (small_Ree_model_Schreier small_Ree_fixed_group_center_trivial
  small_Ree_outer_three_kernel_field_complement)
open CFSG.RankThree (small_Ree_large_prime_field_coset_descent)
open CFSG.RankThree.Chevalley (ringEquiv_eq_one_of_card_eq_prime)
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute)
open CFSG.RankThree.PartTwo.KFacts.KS14 (three_dvd_card_of_reeTitsModel_twistedG2)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def SmallReeOuterIsField
    : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime],
    Nat.card K = 3 ^ (2 * a + 1) → ∀ α : MulAut (ReeTag.G2.reeGamma K a),
      ∃ (x : ReeTag.G2.reeGamma K a) (τ : K ≃+* K),
        α = MulAut.conj x * ReeTag.G2.reeGammaFieldAut K a τ

theorem fieldClauses_smallRee
    {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpΓ : ¬ p ∣ Nat.card (ReeTag.G2.reeGamma K a))
    (hNL : SubfieldNonLocalizedSmallRee) (hW : SmallReeOuterIsField) :
    FieldClauses p (ReeTag.G2.reeGamma K a) := by
  classical
  rintro ⟨α, hα⟩
  have hαout : α ∉ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) :=
    not_mem_inner_range_of_orderOf hpΓ hα
  obtain ⟨hpf, δ, σ, hσ, hconj, hcard, hfixed⟩ :=
    small_Ree_large_prime_field_coset_descent a ha K hK hp hp3 α hα hαout
  have hord : orderOf (ReeTag.G2.reeGammaFieldAut K a σ) = p := by
    rw [← hconj]
    exact (MulEquiv.orderOf_eq (MulAut.conj δ) α).trans hα
  obtain ⟨d, hd⟩ := hpf
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbd : ((2 * a + 1) / p - 1) / 2 = b := by rw [hd', hb]; omega
  rw [hbd] at hfixed
  have hkcard : Nat.card (fixSubfield σ) = 3 ^ (2 * b + 1) := by rw [hcard, hd', hb]
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP (fixSubfield σ) ReeTag.G2.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) =
      (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (((signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.G2.reeGamma K a).subtype (ReeTag.G2.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.G2.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.G2.tag) (fixSubfield σ).subtype)).symm
  have hF : FStarSimple (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      obtain ⟨hs, hn, -⟩ := small_Ree_whole_group_p_components 0 (fixSubfield σ) hkcard
      have hZ := (small_Ree_fixed_group_center_trivial 0 (fixSubfield σ) hkcard).1
      exact (fStarSimple_iff_isFStarSimple _).2
        ((McBride.Nonsolv.L514.isFStarSimple_congr eC).2
          (isFStarSimple_of_derived_simple hZ hs hn))
    · obtain ⟨-, hs, hn⟩ := reeGamma_G2_simple hb1 (fixSubfield σ) hkcard
      have : IsSimpleGroup (ReeTag.G2.reeGamma (fixSubfield σ) b) := hs
      refine fStarSimple_of_simple eC.isSimpleGroup ?_
      obtain ⟨x, y, hxy⟩ := hn
      exact ⟨eC.symm x, eC.symm y, fun h =>
        hxy (eC.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hinner : ∀ ρ : fixSubfield σ ≃+* fixSubfield σ,
      ReeTag.G2.reeGammaFieldAut (fixSubfield σ) b ρ ∈
        OuterAutomorphisms.inner (ReeTag.G2.reeGamma (fixSubfield σ) b) → ρ = 1 := by
    intro ρ hρ
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      exact ringEquiv_eq_one_of_card_eq_prime Nat.prime_three (by simpa using hkcard) ρ
    · obtain ⟨-, -, -, ⟨R, χ, -, hsec, -⟩, -, -⟩ :=
        small_Ree_outer_three_kernel_field_complement b hb1 (fixSubfield σ) hkcard
      have h1 := hsec ρ
      rw [(QuotientGroup.eq_one_iff _).2 hρ, map_one] at h1
      exact h1.symm
  have hNLC := hNL a ha K hK p hp hp3 σ hσ
  have hC : Subgroup.centralizer
      (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) : Set (ReeTag.G2.reeGamma K a)) =
        ⊥ := centralizer_eq_bot_of_nonLocalized hNLC
  have hS : ∀ g : MulAut (ReeTag.G2.reeGamma K a),
      (∀ x ∈ signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ), g x = x) →
        g ∈ Subgroup.zpowers (ReeTag.G2.reeGammaFieldAut K a σ) := fun g hg =>
    mem_zpowers_of_fixes_of_normalForm (fun u v => ringAut_commute u v)
      (ReeTag.G2.reeGammaFieldAutHom K a) (hW a ha K hK) σ _ (fun _ => Iff.rfl) hC
      (fun x τ hx hfix => ree_zpowers_of_inner_on_subfield σ hfixed hinner x τ hx hfix) hg
  exact ⟨_, hord, fixedClauses_of_stabilizer hord hF (fun _ => hNLC) hS⟩

theorem fieldClauses_reeG2
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedG2 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedSmallRee) (hW : SmallReeOuterIsField) :
    FieldClauses p T := by
  have hp3 : 3 < p := by
    have h3 := three_dvd_card_of_reeTitsModel_twistedG2 hm
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f hm
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hm
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.G2.reeGamma K a') := Finite.of_equiv T E.toEquiv
  have hpΓ : ¬ p ∣ Nat.card (ReeTag.G2.reeGamma K a') := by rwa [← Nat.card_congr E.toEquiv]
  exact FieldClauses.of_mulEquiv E.symm (fieldClauses_smallRee ha K hK' hp hp3 hpΓ hNL hW)

theorem nearOrField_reeG2
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : ReeTitsModel T .twistedG2 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedSmallRee) (hW : SmallReeOuterIsField) :
    signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_reeG2 hm hp hp2 hpT hNL hW)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
