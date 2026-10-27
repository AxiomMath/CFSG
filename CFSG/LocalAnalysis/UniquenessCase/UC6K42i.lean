module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42e
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open scoped commutatorElement

theorem isIrreducible_of_invariant_uc6 {F : Type} [Field F] {Γ : Type} [Group Γ] {M : Type}
    [AddCommGroup M] [Module F M] [Nontrivial M] (π : Representation F Γ M)
    (h : ∀ U : Submodule F M, (∀ g : Γ, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    π.IsIrreducible := by
  haveI : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun h' => by
    have := congrArg Subrepresentation.toSubmodule h'
    exact bot_ne_top this⟩
  refine { eq_bot_or_eq_top := fun a => ?_ }
  rcases h a.toSubmodule (fun g u hu => a.apply_mem_toSubmodule g hu) with h0 | h1
  · left
    exact Subrepresentation.toSubmodule_injective h0
  · right
    exact Subrepresentation.toSubmodule_injective h1

variable {G : Type} [Group G] [Finite G]

theorem restrict_data_uc6 {p r : ℕ} [Fact p.Prime] (hr : r.Prime) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) (hQ2 : IsPGroup 2 Q)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (W : Submodule (ZMod p) V)
    (hWinv : ∀ h ∈ Q ⊔ D, ∀ w ∈ W, ρ h w ∈ W) (hWnt : ∃ q ∈ Q, ∃ w ∈ W, ρ q w ≠ w)
    (hWirr : ∀ U : Submodule (ZMod p) V, U ≤ W → (∀ h ∈ Q ⊔ D, ∀ u ∈ U, ρ h u ∈ U) →
      U = ⊥ ∨ U = W) :
    ∃ (G₂ : Type) (_ : Group G₂) (_ : Finite G₂) (ρ₂ : Representation (ZMod p) G₂ ↥W)
      (D₂ Q₂ : Subgroup G₂), Function.Injective ρ₂ ∧ ρ₂.IsIrreducible ∧ Nat.card D₂ = r ∧
      fixV ρ₂ D₂ = ⊥ ∧ IsPGroup 2 Q₂ ∧ Q₂ ≠ ⊥ ∧ D₂ ≤ normalizer (Q₂ : Set G₂) ∧
      ⁅D₂, Q₂⁆ = Q₂ ∧ Q₂ ⊔ D₂ = ⊤ ∧ Nat.card Q₂ ≤ Nat.card Q := by
  classical
  let H : Subgroup G := Q ⊔ D
  have hQH : Q ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  let σ : Subrepresentation (ρ.comp H.subtype) := ⟨W, fun g v hv => hWinv g g.2 v hv⟩
  let ψ : Representation (ZMod p) ↥H ↥W := σ.toRepresentation
  have hψ : ∀ (h : ↥H) (w : ↥W), ((ψ h w : ↥W) : V) = ρ (h : G) (w : V) := fun h w => rfl
  let φ : ↥H →* (Module.End (ZMod p) ↥W)ˣ := ψ.toHomUnits
  let φ' : ↥H →* ↥φ.range := φ.rangeRestrict
  have hφ'surj : Function.Surjective φ' := φ.rangeRestrict_surjective
  let ρ₂ : Representation (ZMod p) ↥φ.range ↥W :=
    (Units.coeHom (Module.End (ZMod p) ↥W)).comp φ.range.subtype
  have hρ₂ : ∀ (h : ↥H) (w : ↥W), ρ₂ (φ' h) w = ψ h w := fun h w => rfl
  haveI : Finite ↥φ.range := Finite.of_surjective φ' hφ'surj
  let Q' : Subgroup ↥H := Q.subgroupOf H
  let D' : Subgroup ↥H := D.subgroupOf H
  have hD'card : Nat.card D' = r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hD
  have hQ'card : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  obtain ⟨q₀, hq₀Q, w₀, hw₀W, hw₀⟩ := hWnt
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    exact hw₀ (map_zero _)
  haveI : Nontrivial ↥W := ⟨⟨w₀, hw₀W⟩, 0, fun h => hw₀0 (congrArg Subtype.val h)⟩
  have hDact : ∀ w : ↥W, (∀ a ∈ D'.map φ', ρ₂ a w = w) → (w : V) ∈ fixV ρ D := by
    intro w hw d hd
    have hdH : d ∈ H := hDH hd
    have h1 : φ' ⟨d, hdH⟩ ∈ D'.map φ' :=
      Subgroup.mem_map_of_mem φ' (Subgroup.mem_subgroupOf.2 hd)
    have h2 := hw _ h1
    rw [hρ₂] at h2
    exact congrArg Subtype.val h2
  refine ⟨↥φ.range, inferInstance, inferInstance, ρ₂, D'.map φ', Q'.map φ', ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact Units.val_injective.comp φ.range.subtype_injective
  ·
    refine isIrreducible_of_invariant_uc6 ρ₂ fun U hU => ?_
    let U' : Submodule (ZMod p) V := U.map W.subtype
    have hU'W : U' ≤ W := Submodule.map_subtype_le W U
    have hU'inv : ∀ h ∈ Q ⊔ D, ∀ u ∈ U', ρ h u ∈ U' := by
      rintro h hh _ ⟨u, hu, rfl⟩
      refine ⟨ψ ⟨h, hh⟩ u, ?_, rfl⟩
      exact hU (φ' ⟨h, hh⟩) u hu
    rcases hWirr U' hU'W hU'inv with h0 | h1
    · left
      apply Submodule.map_injective_of_injective W.injective_subtype
      rw [Submodule.map_bot]
      exact h0
    · right
      apply Submodule.map_injective_of_injective W.injective_subtype
      rw [Submodule.map_subtype_top]
      exact h1
  ·
    have hdvd : Nat.card ↥(D'.map φ') ∣ r := hD'card ▸ Subgroup.card_map_dvd D' φ'
    have hne : Nat.card ↥(D'.map φ') ≠ 1 := by
      intro h1
      have hbot : D'.map φ' = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hwfix : (w₀ : V) ∈ fixV ρ D := by
        refine hDact ⟨w₀, hw₀W⟩ fun a ha => ?_
        rw [hbot, Subgroup.mem_bot] at ha
        rw [ha, map_one]
        rfl
      rw [hfix] at hwfix
      exact hw₀0 ((Submodule.mem_bot _).1 hwfix)
    exact ((Nat.dvd_prime hr).1 hdvd).resolve_left hne
  ·
    rw [eq_bot_iff]
    intro w hw
    have := hDact w hw
    rw [hfix] at this
    exact Subtype.ext ((Submodule.mem_bot _).1 this)
  ·
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ2
    have hdvd : Nat.card ↥(Q'.map φ') ∣ 2 ^ a := by
      rw [← ha, ← hQ'card]
      exact Subgroup.card_map_dvd Q' φ'
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hb
  ·
    intro hbot
    have h1 : φ' ⟨q₀, hQH hq₀Q⟩ ∈ Q'.map φ' :=
      Subgroup.mem_map_of_mem φ' (Subgroup.mem_subgroupOf.2 hq₀Q)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : ρ₂ (φ' ⟨q₀, hQH hq₀Q⟩) ⟨w₀, hw₀W⟩ = ⟨w₀, hw₀W⟩ := by
      rw [h1, map_one]
      rfl
    rw [hρ₂] at h2
    exact hw₀ (congrArg Subtype.val h2)
  ·
    apply le_normalizer_of_invariant_uc6
    rintro _ ⟨d', hd', rfl⟩ _ ⟨q', hq', rfl⟩
    have hd'' : (d' : G) ∈ D := Subgroup.mem_subgroupOf.1 hd'
    have hq'' : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq'
    refine ⟨d' * q' * d'⁻¹, ?_, by simp⟩
    show ((d' * q' * d'⁻¹ : ↥H) : G) ∈ Q
    have := (mem_normalizer_iff.1 (hDQ hd'') (q' : G)).1 hq''
    simpa using this
  ·
    have hcomm' : ⁅D', Q'⁆ = Q' := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDH,
        Subgroup.map_subgroupOf_eq_of_le hQH, hcomm]
    rw [← Subgroup.map_commutator, hcomm']
  ·
    have hsup' : Q' ⊔ D' = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQH hDH]
      exact Subgroup.subgroupOf_self (Q ⊔ D)
    rw [← Subgroup.map_sup, hsup', ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hφ'surj]
  ·
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ2
    have hdvd : Nat.card ↥(Q'.map φ') ∣ Nat.card Q := hQ'card ▸ Subgroup.card_map_dvd Q' φ'
    exact Nat.le_of_dvd Nat.card_pos hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC6
