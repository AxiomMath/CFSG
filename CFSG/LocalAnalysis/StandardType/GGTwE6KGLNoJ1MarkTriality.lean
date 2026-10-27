module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Mark
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem exists_ppd_dvd_ordTrialityD4 {n κ : ℕ} (hn : 1 ≤ n) (hκ : κ = 3 ∨ κ = 6 ∨ κ = 12)
    (h6 : κ * n ≠ 6) : ∃ p, IsPrimitivePrimeDivisor p (κ * n) ∧ p ∣ ordTrialityD4 (2 ^ n) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := κ * n)
    (by rcases hκ with rfl | rfl | rfl <;> omega) h6
  refine ⟨p, hp, ((CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTrialityD4' hn).prim p (κ * n)
    hp (by rcases hκ with rfl | rfl | rfl <;> omega)).2 ?_⟩
  rcases hκ with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨2, by ring⟩)
  · exact Or.inr (Or.inl ⟨1, by ring⟩)
  · exact Or.inl ⟨⟨1, by ring⟩, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩

theorem ordTrialityD4_two_pow_le {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    ordTrialityD4 (2 ^ g) ≤ ordTrialityD4 (2 ^ n) := by
  have h : 2 ^ g ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hn hgn)
  unfold ordTrialityD4
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_left h _) (Nat.pow_le_pow_left h _)) le_rfl))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h _) _)) (Nat.sub_le_sub_right
    (Nat.pow_le_pow_left h _) _)

theorem ordTrialityD4_dvd_card_of_marking {X : Type*} [Group X] {n : ℕ}
    (hmark : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.triD4, 0, n⟩) :
    1 ≤ n ∧ ordTrialityD4 (2 ^ n) ∣ Nat.card X := by
  obtain ⟨-, lab', hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hlab.1
    (twistedChevalleyModel_largeEven .D4 hK)
  refine ⟨hlab.1, ?_⟩
  rw [← (Nat.card_congr θ.toEquiv).trans hc]
  exact Subgroup.card_quotient_dvd_card _

theorem not_largeEvenMarking_triD4_of_card {R : Type} [Group R] {N n : ℕ} (hN : 0 < N)
    (hcard : Nat.card R = N)
    (harith : 1 ≤ n → ¬ ordTrialityD4 (2 ^ n) ∣ N ∨ N ≤ ordTrialityD4 (2 ^ n))
    {J₁ : Subgroup R} (hJ : J₁ ≠ ⊤) :
    ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.triD4, 0, n⟩) := fun hmark => by
  obtain ⟨hn, hd⟩ := ordTrialityD4_dvd_card_of_marking hmark
  exact not_dvd_card_of_ne_top_arith hN hcard (harith hn) hJ hd

theorem largeEvenLabelAll_noJ1_triD4_of_card {lab : LargeEvenLabel} {N : ℕ}
    (hcard : LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = N) (hN : 0 < N)
    (harith : ∀ n : ℕ, 1 ≤ n → Odd n → lab.n ∣ n →
      ¬ ordTrialityD4 (2 ^ n) ∣ N ∨ N ≤ ordTrialityD4 (2 ^ n)) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → 3 ∣ 2 ^ n + 1 →
      lab.n ∣ n → ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.triD4, 0, n⟩) :=
  fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, fun _ n hJ h3 hl =>
    not_largeEvenMarking_triD4_of_card hN hq.2
      (fun hn => harith n hn (odd_of_three_dvd_two_pow_add_one_noJ1 h3) hl) hJ⟩) (hcard Q hQ)

theorem largeEvenLabelAll_noJ1_dPair_of_card {lab : LargeEvenLabel} {N : ℕ}
    (hcard : LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = N) (hN : 0 < N)
    (harithD : ∀ n : ℕ, 1 ≤ n → Odd n → lab.n ∣ n →
      ¬ ordD 4 (2 ^ n) ∣ N ∨ N ≤ ordD 4 (2 ^ n))
    (harithT : ∀ n : ℕ, 1 ≤ n → Odd n → lab.n ∣ n →
      ¬ ordTrialityD4 (2 ^ n) ∣ N ∨ N ≤ ordTrialityD4 (2 ^ n)) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → 3 ∣ 2 ^ n + 1 →
      lab.n ∣ n → ¬ LargeEvenMarking ↥J₁
        (fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩) :=
  fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, fun _ n hJ h3 hl hmark => by
    rcases exists_label_disjunct_marking hmark with hm | hm
    · exact not_largeEvenMarking_D4_of_card hN hq.2
        (fun hn => harithD n hn (odd_of_three_dvd_two_pow_add_one_noJ1 h3) hl) hJ hm
    · exact not_largeEvenMarking_triD4_of_card hN hq.2
        (fun hn => harithT n hn (odd_of_three_dvd_two_pow_add_one_noJ1 h3) hl) hJ hm⟩)
    (hcard Q hQ)

end CFSG.StandardType.SCFourCover

end
