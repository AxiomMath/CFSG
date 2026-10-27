module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1ETypeDet
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem kgLangS1E_typeDet_E6
    {e : ℕ} (he : 1 ≤ e) {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ e)
    {X : Type} [Group X] (ψ : X ≃* ↥(adjointGroup .E6 k)) :
    (∀ (K₀ : Type) [Field K₀] [Finite K₀], IsEmpty (X ≃* ↥(adjointGroup .E7 K₀))) ∧
    (∀ (K₀ : Type) [Field K₀] [Finite K₀] (σ : K₀ ≃+* K₀), orderOf σ = 2 →
      IsEmpty (X ≃* ↥(graphFixedRootGroup TwistTag.E6 K₀ σ.toRingHom))) ∧
    ∀ (K₀ : Type) [Field K₀] [Finite K₀], Nonempty (X ≃* ↥(adjointGroup .E6 K₀)) →
      Nat.card K₀ = 2 ^ e := by
  have hXcard : Nat.card X = CFSG.Open.ordE6 (2 ^ e) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hk]
  have hE6 : CFSG.Blueprint.LieModel X .E6 0 2 e := by
    have hadm : CFSG.Open.StatedLieAdmissible .E6 0 2 e := ⟨Nat.prime_two, he, rfl⟩
    have hCEM : CFSG.Blueprint.ChevalleyExceptionalModel X .E6 2 e :=
      ⟨hadm, ⟨k, inferInstance, inferInstance, hk,
        ⟨ψ.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E6 k).symm⟩⟩⟩
    exact Or.inr (Or.inl ⟨rfl, by decide, hCEM⟩)
  have hnotOdd : ¬ CFSG.Blueprint.OddLieType X :=
    CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hE6 (by decide)
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => absurd h.1 (by decide))
  refine ⟨?_, ?_, ?_⟩
  · intro K₀ _ _
    refine ⟨fun φ => ?_⟩
    have hcard : CFSG.Open.ordE7 (Nat.card K₀) = CFSG.Open.ordE6 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE7 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      exact absurd hcard.symm (CFSG.SeitzReduction.E8Pilot.ordE6_ne_ordE7 he hg)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact absurd (kgLangS1E_oddLieType_of_adjointGroup_E7 hc2 φ) hnotOdd
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
      exact absurd (hXcard.symm.trans hcardφ) (MpTypeDet.ordE6_ne_ordTwistedE6 he hhf)
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      exact absurd
        (kgLangS1E_oddLieType_of_graphFixedRootGroup_E6 hp hp2 hhf hK0' hσpow' φ) hnotOdd
  · intro K₀ _ _ hε
    obtain ⟨φ⟩ := hε
    have hcard : CFSG.Open.ordE6 (Nat.card K₀) = CFSG.Open.ordE6 (2 ^ e) := by
      have h1 : Nat.card X = CFSG.Open.ordE6 (Nat.card K₀) := by
        rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
      exact h1.symm.trans hXcard
    obtain ⟨p, g, hp, hg, hK0⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.exists_card_eq_prime_pow (K := K₀)
    by_cases hp2 : p = 2
    · rw [hp2] at hK0
      rw [hK0] at hcard
      have hge : g = e := MpTypeDet.eq_of_ordE6_eq hg he hcard
      rw [hK0, hge]
    · have hchar : CharP K₀ p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hg hK0
      have hc2 : ringChar K₀ ≠ 2 := fun h => hp2 (ringChar.eq K₀ p ▸ h)
      exact (hnotOdd (kgLangS1E_oddLieType_of_adjointGroup_E6 hc2 φ)).elim

end CFSG.StandardType
