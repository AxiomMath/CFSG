module

public import CFSG.Quasithin.Background.F7TwoE2Comp
public import CFSG.Quasithin.Background.E1Residual

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

theorem mul_self_eq_one_of_card_le_two {Γ : Type*} [Group Γ] [Finite Γ] {B : Subgroup Γ}
    (hB : Nat.card B ≤ 2) {a : Γ} (ha : a ∈ B) : a * a = 1 := by
  by_cases h1 : a = 1
  · simp [h1]
  · have hnt : Nontrivial ↥B := ⟨⟨⟨a, ha⟩, 1, fun h => h1 (congrArg Subtype.val h)⟩⟩
    have h2 : 2 ≤ Nat.card ↥B := Finite.one_lt_card_iff_nontrivial.mpr hnt
    have h3 : Nat.card ↥B = 2 := le_antisymm hB h2
    have h4 : (⟨a, ha⟩ : ↥B) ^ Nat.card ↥B = 1 := pow_card_eq_one'
    rw [h3, pow_two] at h4
    exact congrArg Subtype.val h4

theorem pCoreOf_top_le_solvableRadical {Q : Type*} [Group Q] [Finite Q] :
    pCoreOf 2 (⊤ : Subgroup Q) ≤ CFSG.solvableRadical Q := by
  have hn : (pCoreOf 2 (⊤ : Subgroup Q)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤))
  have hp : IsPGroup 2 ↥(pCoreOf 2 (⊤ : Subgroup Q)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(pCoreOf 2 (⊤ : Subgroup Q)) := hp.isNilpotent
  exact A3.le_solvableRadical hn inferInstance

theorem ne_bot_of_isComponent {Γ : Type*} [Group Γ] {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    L ≠ ⊥ := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

@[expose] def CompInvGen (Q : Type) [Group Q] : Prop :=
  ∀ (L : Subgroup (Q ⧸ CFSG.solvableRadical Q)) (a : Q ⧸ CFSG.solvableRadical Q),
    CFSG.IsComponent L → a * a = 1 →
      a ∈ Subgroup.normalizer (L : Set (Q ⧸ CFSG.solvableRadical Q)) →
      (∃ x ∈ L, a * x ≠ x * a) → InvGen L a

theorem twoResidual_top_le_closure_of_eTwo_gen {Q : Type} [Group Q] [Finite Q]
    (hgen : CompInvGen Q) {S B : Subgroup Q} (h : E1.ETwo Q S B)
    (hB : Nat.card (E1.barRad Q B) ≤ 2) :
    twoResidual (⊤ : Subgroup Q) ≤ Subgroup.closure (nonTwoConj B ⊤) := by
  obtain ⟨-, ha2, -, L, hL, hlayer, hcase⟩ := h
  have hrad : CFSG.solvableRadical (Q ⧸ CFSG.solvableRadical Q) = ⊥ :=
    A3.solvableRadical_quotient_eq_bot Q
  have hLK : L ≤ Subgroup.closure (nonTwoConj (E1.barRad Q B) ⊤) := by
    by_cases hN : E1.barRad Q B ≤ Subgroup.normalizer (L : Set (Q ⧸ CFSG.solvableRadical Q))
    · have hL1 : L = ⁅L, E1.barRad Q B⁆ := by
        rcases hcase with h1 | ⟨h1, -⟩
        · exact h1
        · exact absurd hN h1
      obtain ⟨l, hl, a, ha, hla⟩ : ∃ l ∈ L, ∃ a ∈ E1.barRad Q B, ⁅l, a⁆ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have h3 : ⁅L, E1.barRad Q B⁆ ≤ ⊥ := Subgroup.commutator_le.mpr fun l hl a ha => by
          rw [Subgroup.mem_bot]
          exact hcon l hl a ha
        exact ne_bot_of_isComponent hL (le_bot_iff.mp (hL1 ▸ h3))
      exact le_closure_nonTwoConj_of_invGen ha (hgen L a hL (mul_self_eq_one_of_card_le_two hB ha)
        (hN ha) ⟨l, hl, fun h => hla (commutatorElement_eq_one_iff_mul_comm.mpr h.symm)⟩)
    · obtain ⟨b, hb, hbN⟩ := IsConcreteLE.not_le_iff_exists.mp hN
      exact le_closure_nonTwoConj_of_swap hrad hL hb hbN
  have hlayerK : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) ≤
      Subgroup.closure (nonTwoConj (E1.barRad Q B) ⊤) := by
    rw [hlayer]
    refine iSup₂_le fun t ht x hx => ?_
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have hcomm : ∀ b ∈ E1.barRad Q B, QuotientGroup.mk' (CFSG.solvableRadical Q) t₀ * b =
        b * QuotientGroup.mk' (CFSG.solvableRadical Q) t₀ := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 : ⁅t₀, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup Q) := (E1.mem_tauOf.mp ht₀).2.2 a ha
      have h3 : QuotientGroup.mk' (CFSG.solvableRadical Q) ⁅t₀, a⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (pCoreOf_top_le_solvableRadical h1)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    have hx' : (QuotientGroup.mk' (CFSG.solvableRadical Q) t₀)⁻¹ * x *
        QuotientGroup.mk' (CFSG.solvableRadical Q) t₀ ∈ L := mem_conjSub_iff.mp hx
    have h4 := conj_mem_closure_nonTwoConj hcomm (hLK hx')
    have e : QuotientGroup.mk' (CFSG.solvableRadical Q) t₀ *
        ((QuotientGroup.mk' (CFSG.solvableRadical Q) t₀)⁻¹ * x *
          QuotientGroup.mk' (CFSG.solvableRadical Q) t₀) *
        (QuotientGroup.mk' (CFSG.solvableRadical Q) t₀)⁻¹ = x := by group
    rwa [e] at h4
  have hne : (nonTwoConj (E1.barRad Q B) ⊤).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h5 := hLK
    rw [hemp, Subgroup.closure_empty] at h5
    exact ne_bot_of_isComponent hL (le_bot_iff.mp h5)
  have h2 : ∀ y ∈ (⊤ : Subgroup Q), ∃ k : ℕ, y ^ 2 ^ k ∈ oInftyE Q := fun y _ =>
    E1.exists_pow_mem_of_mem_pCore (M := oInftyE Q)
      (fun q => by rw [ha2]; exact Subgroup.mem_top _) y
  have hres : twoResidual (⊤ : Subgroup Q) ≤ oInftyE Q :=
    twoResidual_le_of_isTwoQuotient le_top
      (top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr inferInstance)) h2
  intro x hx
  exact comap_closure_le_closure_nonTwoConj (CFSG.solvableRadical Q) hne (hlayerK (hres hx))

end CFSG.Quasithin.F7Two
