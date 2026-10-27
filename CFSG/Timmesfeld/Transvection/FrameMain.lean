module

public import CFSG.Timmesfeld.Transvection.QTwo
public import CFSG.Timmesfeld.Transvection.ModelRank

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

@[expose] def TransvectionStatementFrameLarge : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup H) (k : Fin r), IsSmallFrame Δ P Q k →
      ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
        TransvectionConclusionRank H Δ f hf r hr

theorem transvectionStatementFrame_of_card_two {H : Type} [Group H] {Δ : Set (Subgroup H)}
    (h : TransvectionHyp H Δ) {A : Subgroup H} (hA : A ∈ Δ) (h2 : Nat.card A = 2) {r : ℕ}
    (hr : 2 ≤ r) {P Q : Fin r → Subgroup H} {k : Fin r} (hfr : IsSmallFrame Δ P Q k) :
    (∀ X ∈ Δ, Nat.card X = 2 ^ 1) ∧ TransvectionConclusionRank H Δ 1 le_rfl r hr :=
  ⟨fun _ hX => (QTwo.card_eq_two h.cls hA h2 hX).trans (pow_one 2).symm,
    transvectionConclusionRank_of_isSmallFrame (transvectionConclusion_of_card_two h hA h2) hr
      hfr⟩

theorem exists_card_eq_two_pow {H : Type*} [Group H] [Finite H] {Δ : Set (Subgroup H)}
    (hΔ : IsTransvectionClass Δ) {A : Subgroup H} (hA : A ∈ Δ) :
    ∃ n, 1 ≤ n ∧ Nat.card A = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 A := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hΔ.root.mul_self A hA a a.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  refine ⟨n, ?_, hn⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exfalso
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hΔ.root.ne_bot A hA hn
  · exact hpos

theorem transvectionStatementFrame_of_large (h : TransvectionStatementFrameLarge) :
    TransvectionStatementFrame := by
  intro H _ Δ hyp hlines r hr P Q k hfr
  have := hyp.finite
  have hP0 : P ⟨0, by omega⟩ ∈ Δ := hfr.memP _
  by_cases h2 : Nat.card (P ⟨0, by omega⟩) = 2
  · exact ⟨1, le_rfl, (transvectionStatementFrame_of_card_two hyp hP0 h2 hr hfr)⟩
  refine h H Δ hyp hlines (fun A hA => ?_) r hr P Q k hfr
  obtain ⟨n, hn1, hn⟩ := exists_card_eq_two_pow hyp.cls hA
  have hAP : Nat.card A = Nat.card (P ⟨0, by omega⟩) := hyp.cls.root.card_eq hA hP0
  rw [hn] at hAP
  rcases n with _ | _ | n
  · omega
  · exact absurd hAP.symm (by simpa using h2)
  · rw [hn, pow_succ, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

end CFSG.Timmesfeld.Transvection
