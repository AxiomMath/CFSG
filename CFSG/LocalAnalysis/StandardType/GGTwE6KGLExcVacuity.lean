module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1MarkTriality
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoA5
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot.EvenExc

private theorem not_dvd_of_ppd_kglExc {M N e p k : ℕ} {Z : ℕ → Prop} (hN : Profile N e Z)
    (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (hpM : p ∣ M) (hZ : ¬ Z k) : ¬ M ∣ N :=
  fun h => hZ ((hN.prim p k hp hk).mp (hpM.trans h))

private theorem pos_of_profile_kglExc {N e : ℕ} {Z : ℕ → Prop} (h : Profile N e Z) : 0 < N := by
  obtain ⟨r, hr, rfl⟩ := h.two
  exact Nat.mul_pos (by positivity) hr.pos

private theorem dvd_twelve_G2_kglExc {g k : ℕ} (h : k ∣ g * 6 ∨ k ∣ g * 2) : k ∣ g * 12 :=
  h.elim (fun h => h.trans ⟨2, by ring⟩) (fun h => h.trans ⟨6, by ring⟩)

private theorem dvd_twelve_D4_kglExc {g k : ℕ}
    (h : (k ∣ g * 12 ∧ ¬ k ∣ g * 4) ∨ k ∣ g * 6 ∨ k ∣ g * 2) : k ∣ g * 12 :=
  h.elim (·.1) dvd_twelve_G2_kglExc

private theorem dvd_twelve_F4_kglExc {g k : ℕ} (h : (k ∣ 2 * (g * 6) ∧ ¬ k ∣ g * 6) ∨
    k ∣ g * 4 ∨ (k ∣ 2 * (g * 3) ∧ ¬ k ∣ g * 3) ∨ k ∣ g) : k ∣ g * 12 := by
  rcases h with ⟨h, -⟩ | h | ⟨h, -⟩ | h
  · exact h.trans ⟨1, by ring⟩
  · exact h.trans ⟨3, by ring⟩
  · exact h.trans ⟨2, by ring⟩
  · exact h.trans ⟨12, by ring⟩

private theorem aPair_arith_kglExc {N e g : ℕ} {Z : ℕ → Prop} (hN : Profile N e Z)
    (hZ : ∀ k, Z k → k ∣ g * 12) (h3 : ¬ 3 ∣ g) (n : ℕ) (hn : 1 ≤ n) :
    ¬ ordA 2 (2 ^ (3 * n)) ∣ N ∧ ¬ ordTwistedA 2 (2 ^ (3 * n)) ∣ N := by
  have key : ∀ k, 9 ∣ k → ¬ Z k := fun k h9 hk => h3 (by have := h9.trans (hZ k hk); omega)
  obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordA_two_nine hn
  obtain ⟨p', hp', hpM'⟩ := exists_ppd_dvd_ordTwistedA_two_eighteen hn
  exact ⟨not_dvd_of_ppd_kglExc hN hp (by omega) hpM (key _ ⟨n, rfl⟩),
    not_dvd_of_ppd_kglExc hN hp' (by omega) hpM' (key _ ⟨2 * n, by ring⟩)⟩

private theorem not_Z_G2_kglExc {g k : ℕ} (hg : Odd g) (h4 : 4 ∣ k) :
    ¬ (k ∣ g * 6 ∨ k ∣ g * 2) := by
  obtain ⟨j, rfl⟩ := hg
  rintro (h | h) <;> · have := h4.trans h; omega

private theorem dPair_G2_kglExc {g n : ℕ} (hg : 1 ≤ g) (hn : Odd n) (hgn : g ∣ n) :
    ¬ ordD 4 (2 ^ n) ∣ ordG2 (2 ^ g) ∧ ¬ ordTrialityD4 (2 ^ n) ∣ ordG2 (2 ^ g) := by
  have hgo : Odd g := hn.of_dvd_nat hgn
  have := hn.pos
  obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordD_four (κ := 4) hn.pos (Or.inr (Or.inl rfl))
    (by omega)
  obtain ⟨p', hp', hpM'⟩ := exists_ppd_dvd_ordTrialityD4 (κ := 12) hn.pos (Or.inr (Or.inr rfl))
    (by omega)
  exact ⟨not_dvd_of_ppd_kglExc (profile_ordG2' hg) hp (by omega) hpM
      (not_Z_G2_kglExc hgo ⟨n, rfl⟩),
    not_dvd_of_ppd_kglExc (profile_ordG2' hg) hp' (by omega) hpM'
      (not_Z_G2_kglExc hgo ⟨3 * n, by ring⟩)⟩

private theorem not_ordD_four_dvd_ordTrialityD4_kglExc {g n : ℕ} (hg : 1 ≤ g) (hn : Odd n)
    (hgn : g ∣ n) : ¬ ordD 4 (2 ^ n) ∣ ordTrialityD4 (2 ^ g) := by
  have hgo : Odd g := hn.of_dvd_nat hgn
  obtain ⟨c, rfl⟩ := hgn
  have hc : Odd c := (Nat.odd_mul.mp hn).2
  rcases Nat.lt_or_ge c 3 with h | h
  · obtain rfl : c = 1 := by obtain ⟨j, rfl⟩ := hc; omega
    rw [mul_one]
    obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordD_four (κ := 4) hg (Or.inr (Or.inl rfl)) (by omega)
    refine not_dvd_of_ppd_kglExc (profile_ordTrialityD4' hg) hp (by omega) hpM ?_
    rintro (⟨-, h⟩ | h)
    · exact h ⟨1, by ring⟩
    · exact not_Z_G2_kglExc hgo ⟨g, rfl⟩ h
  · have h3 : g * 3 ≤ g * c := Nat.mul_le_mul_left g h
    obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordD_four (κ := 6) (n := g * c) (by omega)
      (Or.inr (Or.inr rfl)) (by omega)
    refine not_dvd_of_ppd_kglExc (profile_ordTrialityD4' hg) hp (by omega) hpM ?_
    rintro (⟨h, -⟩ | h | h) <;> · have := Nat.le_of_dvd (by omega) h; omega

private theorem not_Z_F4_three_kglExc {g n : ℕ} (hg : 1 ≤ g) (hn : Odd n) (hgn : g ∣ n) :
    ¬ ((3 * n ∣ 2 * (g * 6) ∧ ¬ 3 * n ∣ g * 6) ∨ 3 * n ∣ g * 4 ∨
      (3 * n ∣ 2 * (g * 3) ∧ ¬ 3 * n ∣ g * 3) ∨ 3 * n ∣ g) := by
  have hcop : Nat.Coprime n 4 := by simpa using Nat.Coprime.pow_right 2 hn.coprime_two_right
  have heq : n ∣ g * 4 → n = g := fun h => Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right h) hgn
  have h3 : 3 * n ∣ 3 * (g * 4) → n = g := fun h =>
    heq (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h)
  rintro (⟨h, h'⟩ | h | ⟨h, h'⟩ | h)
  · obtain rfl := h3 (h.trans ⟨1, by ring⟩)
    exact h' ⟨2, by ring⟩
  · obtain rfl := heq ((Dvd.intro_left 3 rfl).trans h)
    obtain ⟨t, ht⟩ := h
    have : 4 = 3 * t := Nat.eq_of_mul_eq_mul_left hn.pos (by rw [ht]; ring)
    omega
  · obtain rfl := h3 (h.trans ⟨2, by ring⟩)
    exact h' ⟨1, by ring⟩
  · have := Nat.le_of_dvd (by omega) h
    have := Nat.le_of_dvd hn.pos hgn
    omega

private theorem dPair_F4_kglExc {g n : ℕ} (hg : 1 ≤ g) (hn : Odd n) (hgn : g ∣ n) :
    ¬ ordD 4 (2 ^ n) ∣ ordTwistedF4 (2 ^ g) ∧ ¬ ordTrialityD4 (2 ^ n) ∣ ordTwistedF4 (2 ^ g) := by
  have := hn.pos
  have h6 : 3 * n ≠ 6 := by obtain ⟨j, rfl⟩ := hn; omega
  obtain ⟨p, hp, hpM⟩ := exists_ppd_dvd_ordD_four (κ := 3) hn.pos (Or.inl rfl) h6
  obtain ⟨p', hp', hpM'⟩ := exists_ppd_dvd_ordTrialityD4 (κ := 3) hn.pos (Or.inl rfl) h6
  have hZ := not_Z_F4_three_kglExc hg hn hgn
  exact ⟨not_dvd_of_ppd_kglExc (profile_ordTwistedF4' hg) hp (by omega) hpM hZ,
    not_dvd_of_ppd_kglExc (profile_ordTwistedF4' hg) hp' (by omega) hpM' hZ⟩

private theorem largeEvenLabelAll_card_G2_kglExc {lab : LargeEvenLabel} (htag : lab.tag = .G2) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordG2 (2 ^ lab.n) := by
  obtain ⟨t, N, g⟩ := lab
  dsimp only at htag ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2
    (untwistedChevalleyModel_largeEven .G2 hK)⟩

private theorem largeEvenLabelAll_card_triD4_kglExc {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .triD4) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordTrialityD4 (2 ^ lab.n) := by
  obtain ⟨t, N, g⟩ := lab
  have hg : 1 ≤ g := hlab.1
  dsimp only at htag ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two
    hg (twistedChevalleyModel_largeEven .D4 hK)⟩

private theorem largeEvenLabelAll_card_twF4_kglExc {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordTwistedF4 (2 ^ lab.n) := by
  refine (largeEvenLabelAll_markedModel_f4e6 hlab (Or.inr (Or.inl htag))).mono
    fun R _ _ _ hM => ?_
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag ⊢
  subst htag
  have hM' : LieModel R .twistedF4 0 2 g := hM
  rcases hM' with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact card_of_reeTitsModel_twistedF4' hrt
  · exact absurd hsz (by decide)

theorem largeEvenLabelAll_noJ1_dPair_exc {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → 3 ∣ 2 ^ n + 1 →
      lab.n ∣ n → ¬ LargeEvenMarking ↥J₁
        (fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩) := by
  have hg : 1 ≤ lab.n := hlab.1
  rcases htag with h | h | h
  · exact largeEvenLabelAll_noJ1_dPair_of_card (largeEvenLabelAll_card_G2_kglExc h)
      (pos_of_profile_kglExc (profile_ordG2' hg))
      (fun _ _ hn hgn => Or.inl (dPair_G2_kglExc hg hn hgn).1)
      (fun _ _ hn hgn => Or.inl (dPair_G2_kglExc hg hn hgn).2)
  · exact largeEvenLabelAll_noJ1_dPair_of_card (largeEvenLabelAll_card_triD4_kglExc hlab h)
      (pos_of_profile_kglExc (profile_ordTrialityD4' hg))
      (fun _ _ hn hgn => Or.inl (not_ordD_four_dvd_ordTrialityD4_kglExc hg hn hgn))
      (fun _ hn _ hgn => Or.inr (ordTrialityD4_two_pow_le hn hgn))
  · exact largeEvenLabelAll_noJ1_dPair_of_card (largeEvenLabelAll_card_twF4_kglExc hlab h)
      (pos_of_profile_kglExc (profile_ordTwistedF4' hg))
      (fun _ _ hn hgn => Or.inl (dPair_F4_kglExc hg hn hgn).1)
      (fun _ _ hn hgn => Or.inl (dPair_F4_kglExc hg hn hgn).2)

theorem largeEvenLabelAll_noJ1_aPair_exc {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4) (h3 : ¬ 3 ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → 3 ∣ 2 ^ n + 1 →
      lab.n ∣ 3 * n → ¬ LargeEvenMarking ↥J₁
        (fun lab' _ _ _ _ _ => lab' = ⟨.A, 2, 3 * n⟩ ∨ lab' = ⟨.twA, 2, 3 * n⟩) := by
  have hg : 1 ≤ lab.n := hlab.1
  obtain ⟨N, hc, e, Z, hP, hZ⟩ : ∃ N, (LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = N) ∧
      ∃ e Z, Profile N e Z ∧ ∀ k, Z k → k ∣ lab.n * 12 := by
    rcases htag with h | h | h
    · exact ⟨_, largeEvenLabelAll_card_G2_kglExc h, _, _, profile_ordG2' hg,
        fun _ => dvd_twelve_G2_kglExc⟩
    · exact ⟨_, largeEvenLabelAll_card_triD4_kglExc hlab h, _, _, profile_ordTrialityD4' hg,
        fun _ => dvd_twelve_D4_kglExc⟩
    · exact ⟨_, largeEvenLabelAll_card_twF4_kglExc hlab h, _, _, profile_ordTwistedF4' hg,
        fun _ => dvd_twelve_F4_kglExc⟩
  exact largeEvenLabelAll_noJ1_aPair_of_card hc (pos_of_profile_kglExc hP)
    (fun n hn _ _ => Or.inl (aPair_arith_kglExc hP hZ h3 n hn).1)
    (fun n hn _ _ => Or.inl (aPair_arith_kglExc hP hZ h3 n hn).2)

end CFSG.StandardType.SCFourCover

end
