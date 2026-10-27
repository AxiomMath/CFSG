module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPlainOrderCard
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPlainOrderPSU
import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem ordG2_bound_plainOrd {q : ℕ} (hq : 2 ≤ q) :
    0 < CFSG.Open.ordG2 q ∧ CFSG.Open.ordG2 q ≤ q ^ 29 := by
  have h6 : 2 ≤ q ^ 6 := hq.trans (Nat.le_self_pow (by norm_num) q)
  have h2 : 2 ≤ q ^ 2 := hq.trans (Nat.le_self_pow (by norm_num) q)
  unfold CFSG.Open.ordG2
  refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega), ?_⟩
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le _ _)) (Nat.sub_le _ _)
    _ = q ^ 14 := by ring
    _ ≤ q ^ 29 := Nat.pow_le_pow_right (by omega) (by norm_num)

private theorem ordTrialityD4_bound_plainOrd {q : ℕ} (hq : 2 ≤ q) :
    0 < CFSG.Open.ordTrialityD4 q ∧ CFSG.Open.ordTrialityD4 q ≤ q ^ 29 := by
  have h6 : 2 ≤ q ^ 6 := hq.trans (Nat.le_self_pow (by norm_num) q)
  have h2 : 2 ≤ q ^ 2 := hq.trans (Nat.le_self_pow (by norm_num) q)
  have h4 : 2 ≤ q ^ 4 := hq.trans (Nat.le_self_pow (by norm_num) q)
  have h9 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
    have a : q ^ 8 * 2 ≤ q ^ 8 * q := Nat.mul_le_mul_left _ hq
    have b : q ^ 4 * 2 ≤ q ^ 4 * q ^ 4 := Nat.mul_le_mul_left _ h4
    have e8 : q ^ 8 = q ^ 4 * q ^ 4 := by ring
    have e9 : q ^ 9 = q ^ 8 * q := by ring
    omega
  unfold CFSG.Open.ordTrialityD4
  refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega), ?_⟩
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 9 * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h9) (Nat.sub_le _ _))
          (Nat.sub_le _ _)
    _ = q ^ 29 := by ring

private theorem finite_card_lt_plainOrd {R : Type} {g x : ℕ} (hg : 1 ≤ g)
    (hc : Nat.card R = x) (hx : 0 < x ∧ x ≤ (2 ^ g) ^ 29) :
    Finite R ∧ Nat.card R < CFSG.Open.ordTwistedA 5 (2 ^ g) := by
  refine ⟨Nat.finite_of_card_ne_zero (by omega), ?_⟩
  rw [hc]
  exact hx.2.trans_lt (pow_twentyNine_lt_ordTwistedA_five hg)

theorem not_largeEvenMarking_twA_five_of_card_lt {R : Type} [Group R] [Finite R] {g : ℕ}
    (hR : Nat.card R < CFSG.Open.ordTwistedA 5 (2 ^ g)) (J : Subgroup R) {n : ℕ} (hgn : g ∣ n) :
    ¬ LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := fun hmark => by
  obtain ⟨hn, hdvd⟩ := ordTwistedA_five_dvd_card_of_twA_marking hmark
  have h1 := Nat.le_of_dvd Nat.card_pos hdvd
  have h2 := ordTwistedA_five_two_pow_le_of_dvd hn hgn
  omega

theorem largeEvenLabelAll_not_marking_twA_five_of_card_lt {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ _ _ =>
      Finite R ∧ Nat.card R < CFSG.Open.ordTwistedA 5 (2 ^ lab.n)) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) :=
  h.mono fun _ _ _ _ hR J₁ _ _ hgn => by
    haveI := hR.1
    exact not_largeEvenMarking_twA_five_of_card_lt hR.2 J₁ hgn

theorem largeEvenLabelAll_not_marking_twA_five_plainOrder {lab : LargeEvenLabel}
    (h : (lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank ≤ 4)) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) :=
  largeEvenLabelAll_not_marking_twA_five_of_card_lt
    (largeEvenLabelAll_card_lt_ordTwistedA_five_classical h)


theorem largeEvenLabelAll_not_marking_twA_five_exceptional {lab : LargeEvenLabel}
    (h : lab.tag = .G2 ∨ lab.tag = .triD4) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  refine largeEvenLabelAll_not_marking_twA_five_of_card_lt ?_
  obtain ⟨t, N, g⟩ := lab
  dsimp only at h ⊢
  intro Q hQ
  rcases h with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    have hg : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with rfl | h0
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · exact h0
    exact finite_card_lt_plainOrd hg
      (CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2
        (untwistedChevalleyModel_largeEven .G2 hK))
      (ordG2_bound_plainOrd (Nat.one_lt_two_pow (by omega)))
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    have hg : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with rfl | h0
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · exact h0
    exact finite_card_lt_plainOrd hg
      (CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hg
        (twistedChevalleyModel_largeEven .D4 hK))
      (ordTrialityD4_bound_plainOrd (Nat.one_lt_two_pow (by omega)))

end CFSG.StandardType.SCFourCover
