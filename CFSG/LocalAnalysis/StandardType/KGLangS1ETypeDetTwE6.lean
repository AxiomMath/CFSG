module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1ETypeDet
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem kgLangS1E_typeDet_twE6
    {e : ℕ} (he : 1 ≤ e) {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {X : Type} [Group X] (ψ : X ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) :
    (∀ (K₀ : Type) [Field K₀] [Finite K₀], IsEmpty (X ≃* ↥(adjointGroup .E6 K₀))) ∧
    (∀ (K₀ : Type) [Field K₀] [Finite K₀], IsEmpty (X ≃* ↥(adjointGroup .E7 K₀))) ∧
    ∀ (K₀ : Type) [Field K₀] [Finite K₀] (σ₀ : K₀ ≃+* K₀), orderOf σ₀ = 2 →
      Nonempty (X ≃* ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom)) →
      Nat.card K₀ = (2 ^ e) ^ 2 := by
  have hXcard : Nat.card X = CFSG.Open.ordTwistedE6 (2 ^ e) := by
    rw [Nat.card_congr ψ.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two he hk σ.toRingHom hσ]
  have hTwE6 : CFSG.Blueprint.LieModel X .twistedE6 0 2 e := by
    have hadm : CFSG.Open.StatedLieAdmissible .twistedE6 0 2 e := ⟨Nat.prime_two, he, rfl⟩
    have hK' : Nat.card k = (2 ^ e) ^ TwistTag.E6.order := by rw [hk]; rfl
    obtain ⟨e'⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv
      TwistTag.E6 Nat.prime_two he k hK' σ.toRingHom hσ
    have hCEM : CFSG.Blueprint.ChevalleyExceptionalModel X .twistedE6 2 e :=
      ⟨hadm, ⟨k, inferInstance, inferInstance, hK', σ.toRingHom, hσ, ⟨ψ.trans e'.symm⟩⟩⟩
    exact Or.inr (Or.inl ⟨rfl, by decide, hCEM⟩)
  have hnotOdd : ¬ CFSG.Blueprint.OddLieType X :=
    CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hTwE6 (by decide)
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => absurd h.1 (by decide))
  refine ⟨?_, ?_, ?_⟩
  · intro K₀ _ _
    refine ⟨fun φ => ?_⟩
    have hcard : CFSG.Open.ordE6 (Nat.card K₀) = CFSG.Open.ordTwistedE6 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE6 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      exact absurd hcard (MpTypeDet.ordE6_ne_ordTwistedE6 hg he)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact absurd (kgLangS1E_oddLieType_of_adjointGroup_E6 hc2 φ) hnotOdd
  · intro K₀ _ _
    refine ⟨fun φ => ?_⟩
    have hcard : CFSG.Open.ordE7 (Nat.card K₀) = CFSG.Open.ordTwistedE6 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE7 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      exact absurd hcard.symm (CFSG.SeitzReduction.E8Pilot.ordTwistedE6_ne_ordE7 he hg)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact absurd (kgLangS1E_oddLieType_of_adjointGroup_E7 hc2 φ) hnotOdd
  · intro K₀ _ _ σ₀ hσord hε
    obtain ⟨φ⟩ := hε
    have hσ2 : σ₀ ^ 2 = 1 := by rw [← hσord, pow_orderOf_eq_one]
    have hσ1 : σ₀ ≠ 1 := by
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
    have hσpow' : ∀ c, σ₀.toRingHom c = c ^ (p ^ (g / 2)) := fun c => hσpow c
    by_cases hp2 : p = 2
    · rw [hp2] at hK0' hσpow'
      have hcardφ : Nat.card X = CFSG.Open.ordTwistedE6 (2 ^ (g / 2)) := by
        rw [Nat.card_congr φ.toEquiv,
          CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two hhf hK0'
            σ₀.toRingHom hσpow']
      have hge : g / 2 = e :=
        MpTypeDet.eq_of_ordTwistedE6_eq hhf he (hcardφ.symm.trans hXcard)
      rw [hK0', hge]
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      exact absurd
        (kgLangS1E_oddLieType_of_graphFixedRootGroup_E6 hp hp2 hhf hK0' hσpow' φ) hnotOdd

end CFSG.StandardType

end
