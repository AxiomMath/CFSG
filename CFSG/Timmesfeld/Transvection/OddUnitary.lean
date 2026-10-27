module

public import CFSG.Timmesfeld.Transvection.GenerateFrameLarge
public import CFSG.Timmesfeld.Transvection.OneOrAll

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

@[expose] def OddUnitaryStatement : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    (∀ A ∈ Δ, 4 ≤ Nat.card A) →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup H) (k : Fin r), IsMaxFrame Δ P Q →
      ¬ IsSmallFrame Δ P Q k →
      ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
        ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * r + 1)) →* H,
          Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
            ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf)
              (2 * r + 1)).rootGroup (unitaryLongRoot (2 * r + 1) (by omega))) g).map Φ

theorem transvectionStatement_of_oddUnitary (h : OddUnitaryStatement) : TransvectionStatement := by
  intro H _ Δ hyp
  haveI : Finite H := hyp.finite
  obtain ⟨A, hA, -⟩ := hyp.rank
  by_cases h2 : Nat.card A = 2
  · exact ⟨1, le_rfl,
      fun X hX => (QTwo.card_eq_two hyp.cls hA h2 hX).trans (pow_one 2).symm,
      transvectionConclusion_of_card_two hyp hA h2⟩
  ·
    have hq : ∀ X ∈ Δ, 4 ≤ Nat.card X := by
      intro X hX
      obtain ⟨n, hn1, hn⟩ := exists_card_eq_two_pow hyp.cls hX
      have hXA : Nat.card X = Nat.card A := hyp.cls.root.card_eq hX hA
      rw [hn] at hXA
      rcases n with _ | _ | n
      · omega
      · exact absurd hXA.symm (by simpa using h2)
      · rw [hn, pow_succ, pow_succ]
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
    have hlines : MeetsLines Δ := hyp.meetsLines hq
    obtain ⟨r, hr, P, Q, hmax⟩ := exists_isMaxFrame hyp hlines
    let k : Fin r := ⟨0, by omega⟩
    by_cases hsmall : IsSmallFrame Δ P Q k
    ·
      obtain ⟨f, hf, hcard, hrank⟩ :=
        transvectionStatementFrameLarge H Δ hyp hlines hq r hr P Q k hsmall
      exact ⟨f, hf, hcard, transvectionConclusion_of_rank hrank⟩
    ·
      obtain ⟨f, hf, hcard, Φ, hsurj, hker, hmem⟩ :=
        h H Δ hyp hlines hq r hr P Q k hmax hsmall
      exact ⟨f, hf, hcard, Or.inr ⟨2 * r + 1, by omega, Φ, hsurj, hker, hmem⟩⟩

end CFSG.Timmesfeld.Transvection
