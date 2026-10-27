module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem kgLangS1E_oddLieType_of_adjointGroup_E6
    {X K : Type} [Group X] [Field K] [Finite K] (hc2 : ringChar K ≠ 2)
    (e : X ≃* ↥(adjointGroup .E6 K)) : CFSG.Blueprint.OddLieType X := by
  obtain ⟨p, f, hp, hf, hK⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K)
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hp2 : p ≠ 2 := fun h => hc2 (by rw [ringChar.eq K p, h])
  have hadm : CFSG.Open.StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  have hmodel : CFSG.Blueprint.UntwistedChevalleyModel X .E6 (p ^ f) :=
    ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E6 K).symm⟩⟩
  exact ⟨.E6, 0, p, f, hp, hp2, hadm,
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, hmodel⟩⟩)⟩

theorem kgLangS1E_oddLieType_of_adjointGroup_E7
    {X K : Type} [Group X] [Field K] [Finite K] (hc2 : ringChar K ≠ 2)
    (e : X ≃* ↥(adjointGroup .E7 K)) : CFSG.Blueprint.OddLieType X := by
  obtain ⟨p, f, hp, hf, hK⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K)
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hp2 : p ≠ 2 := fun h => hc2 (by rw [ringChar.eq K p, h])
  have hadm : CFSG.Open.StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  have hmodel : CFSG.Blueprint.UntwistedChevalleyModel X .E7 (p ^ f) :=
    ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E7 K).symm⟩⟩
  exact ⟨.E7, 0, p, f, hp, hp2, hadm,
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, hmodel⟩⟩)⟩

theorem kgLangS1E_oddLieType_of_graphFixedRootGroup_E6
    {X K : Type} [Group X] [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : X ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ)) : CFSG.Blueprint.OddLieType X := by
  have hK' : Nat.card K = (p ^ f) ^ TwistTag.E6.order := by rw [hK]; rfl
  obtain ⟨e'⟩ :=
    CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.E6 hp hf K hK' σ hσ
  have htw : CFSG.Blueprint.TwistedChevalleyModel X .E6 (p ^ f) :=
    ⟨K, inferInstance, inferInstance, hK', σ, hσ, ⟨e.trans e'.symm⟩⟩
  have hadm : CFSG.Open.StatedLieAdmissible .twistedE6 0 p f := ⟨hp, hf, rfl⟩
  exact ⟨.twistedE6, 0, p, f, hp, hp2, hadm,
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, htw⟩⟩)⟩

theorem kgLangS1E_typeDet_E7
    {e : ℕ} (he : 1 ≤ e) {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ e)
    {X : Type} [Group X] (ψ : X ≃* ↥(adjointGroup .E7 k)) :
    (∀ (K₀ : Type) [Field K₀] [Finite K₀], IsEmpty (X ≃* ↥(adjointGroup .E6 K₀))) ∧
    (∀ (K₀ : Type) [Field K₀] [Finite K₀] (σ : K₀ ≃+* K₀), orderOf σ = 2 →
      IsEmpty (X ≃* ↥(graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom))) ∧
    ∀ (K₀ : Type) [Field K₀] [Finite K₀], Nonempty (X ≃* ↥(adjointGroup .E7 K₀)) →
      Nat.card K₀ = 2 ^ e := by
  have hXcard : Nat.card X = CFSG.Open.ordE7 (2 ^ e) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hk]
  have hE7 : CFSG.Blueprint.LieModel X .E7 0 2 e := by
    have hadm : CFSG.Open.StatedLieAdmissible .E7 0 2 e := ⟨Nat.prime_two, he, rfl⟩
    have hCEM : CFSG.Blueprint.ChevalleyExceptionalModel X .E7 2 e :=
      ⟨hadm, ⟨k, inferInstance, inferInstance, hk,
        ⟨ψ.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E7 k).symm⟩⟩⟩
    exact Or.inr (Or.inl ⟨rfl, by decide, hCEM⟩)
  have hnotOdd : ¬ CFSG.Blueprint.OddLieType X :=
    CFSG.SeitzReduction.CrossChar.e7NotOddLieInput X e hE7
  refine ⟨?_, ?_, ?_⟩
  · intro K₀ _ _
    refine ⟨fun φ => ?_⟩
    have hcard : CFSG.Open.ordE6 (Nat.card K₀) = CFSG.Open.ordE7 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE6 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      exact absurd hcard (CFSG.SeitzReduction.E8Pilot.ordE6_ne_ordE7 hg he)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact absurd (kgLangS1E_oddLieType_of_adjointGroup_E6 hc2 φ) hnotOdd
  · intro K₀ _ _ σ hσord
    refine ⟨fun φ => ?_⟩
    have hσ2 : σ ^ 2 = 1 := by rw [← hσord, pow_orderOf_eq_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hσord
      exact absurd hσord (by norm_num)
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    obtain ⟨hgev, hσpow, -⟩ := ringEquiv_sq_eq_one_facts hp hg hK0 hσ2 hσ1
    obtain ⟨h, hg_eq⟩ := even_iff_two_dvd.mp hgev
    have hgt : g / 2 = h := by omega
    have hhf : 1 ≤ g / 2 := by rw [hgt]; omega
    have hK0' : Nat.card K₀ = (p ^ (g / 2)) ^ 2 := by
      rw [hgt, hK0, show g = h * 2 by omega, pow_mul]
    have hσpow' : ∀ c, σ.toRingHom c = c ^ (p ^ (g / 2)) := fun c => hσpow c
    by_cases hp2 : p = 2
    · rw [hp2] at hK0' hσpow'
      have hcardφ : Nat.card X = CFSG.Open.ordTwistedE6 (2 ^ (g / 2)) := by
        rw [Nat.card_congr φ.toEquiv,
          CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two hhf hK0'
            σ.toRingHom hσpow']
      exact absurd (hcardφ.symm.trans hXcard)
        (CFSG.SeitzReduction.E8Pilot.ordTwistedE6_ne_ordE7 hhf he)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      exact absurd (kgLangS1E_oddLieType_of_graphFixedRootGroup_E6 hp hp2 hhf hK0' hσpow' φ) hnotOdd
  · intro K₀ _ _ hε
    obtain ⟨φ⟩ := hε
    have hcard : CFSG.Open.ordE7 (Nat.card K₀) = CFSG.Open.ordE7 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE7 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      have hge : g = e := CFSG.SeitzReduction.E8Pilot.eq_of_ordE7_eq hg he hcard
      rw [hK0, hge]
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact (hnotOdd (kgLangS1E_oddLieType_of_adjointGroup_E7 hc2 φ)).elim

end CFSG.StandardType
