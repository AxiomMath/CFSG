module

public import CFSG.Quasithin.EmptyFaithful.S152He7Nat
public import CFSG.Quasithin.EmptyFaithful.S152He6AutL2
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique He6

@[expose] def PureShapeSeven : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (P : PairData W) (Tb Vb : Subgroup (MulAut W))
    (τ : MulAut W),
    IsL2Prime 7 ↥P.A → SQTKGroup ↥P.Xb → P.A ≤ P.Xb → P.A' ≤ P.Xb → Tb ≤ P.Xb → IsPGroup 2 Tb →
    (∀ S : Subgroup (MulAut W), S ≤ P.Xb → IsPGroup 2 S → ∃ g ∈ P.Xb, ∀ s ∈ S, g * s * g⁻¹ ∈ Tb) →
    (∀ x ∈ P.Xb, ∃ κ ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = κ * s) →
    (∀ Q' : Subgroup (MulAut W), Q' ≤ P.Xb → (Q'.subgroupOf P.Xb).Normal → IsPGroup 2 Q' →
      Q' = ⊥) →
    τ ∈ Tb → (∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A') → (∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A) →
    Vb ≤ Tb → (∀ s ∈ Tb, ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb) → Vb ≠ ⊥ →
    (∀ v ∈ Vb, Nat.card (cmt v ⊤) ≤ 4) →
    ∀ g ∈ P.Xb, (∀ x, x ∈ P.A ↔ g * x * g⁻¹ ∈ P.A) →
      ∃ l ∈ P.A, ∀ x ∈ P.A, g * x * g⁻¹ = l * x * l⁻¹

theorem pureShapeSeven_of_b42
    (hB42 : AsB42) :
    PureShapeSeven := by
  intro W _ _ P Tb Vb τ hA7 hSQ hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hτA' hVT hVn hVne hz
  obtain ⟨e7⟩ := hA7
  have h168 : Nat.card ↥P.A = 168 := by
    rw [Nat.card_congr e7.toEquiv]
    exact CFSG.LocalAnalysis.ComponentInitial.card_PSL_two_zmod_seven
  have hfam : FamPSL ↥P.A := Or.inr ⟨7, Nat.prime_seven, by norm_num, ⟨e7⟩⟩
  have hK : Vb ⊓ (P.A ⊔ P.A') ≠ ⊥ := by
    intro hK
    obtain ⟨v, hvV, hv1, hvc⟩ := exists_central_of_normal hT2 hVT hVn hVne
    have hvK := P.caseB_mem autL2SylowInner_holds hAX hA'X hTX hT2 hconj2 hXKT hO2 hτ hτA hfam
      (hVT hvV) hvc
    have : v ∈ Vb ⊓ (P.A ⊔ P.A') := ⟨hvV, hvK⟩
    rw [hK, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨a, ha, a', ha', -, ha'2, ha1, ha'1, hmem⟩ :=
    P.exists_pair_of_inf_ne_bot hT2 hVT hVn hτ (fun x hx => (hτA x).1 hx)
      (fun x hx => (hτA' x).1 hx) hK
  exact He7.noOuter_of_goodPair hB42 P h168 hSQ hAX ⟨ha, ha', ha1, ha'1, ha'2, hz _ hmem⟩

end CFSG.Quasithin
