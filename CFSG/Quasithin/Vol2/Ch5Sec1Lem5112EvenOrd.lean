module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.Quasithin.H13.EvenOrd

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders

structure Excl (m : ℕ) : Prop where
  psl : ∀ n f, 1 ≤ n → 1 ≤ f → (n, f) ≠ (1, 1) → ordA n (2 ^ f) ≠ m
  psu : ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → ordTwistedA n (2 ^ f) ≠ m
  psp : ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → ordBC n (2 ^ f) ≠ m
  omegaPlus : ∀ n f, 4 ≤ n → 1 ≤ f → ordD n (2 ^ f) ≠ m
  omegaMinus : ∀ n f, 4 ≤ n → 1 ≤ f → ordTwistedD n (2 ^ f) ≠ m
  g2 : ∀ f, 2 ≤ f → ordG2 (2 ^ f) ≠ m
  d4 : ∀ f, 1 ≤ f → ordTrialityD4 (2 ^ f) ≠ m
  f4 : ∀ f, 1 ≤ f → ordF4 (2 ^ f) ≠ m
  e6 : ∀ f, 1 ≤ f → ordE6 (2 ^ f) ≠ m
  e6' : ∀ f, 1 ≤ f → ordTwistedE6 (2 ^ f) ≠ m
  e7 : ∀ f, 1 ≤ f → ordE7 (2 ^ f) ≠ m
  e8 : ∀ f, 1 ≤ f → ordE8 (2 ^ f) ≠ m
  sz : ∀ f, f % 2 = 1 → 3 ≤ f → ordSuzuki (2 ^ f) ≠ m
  twistedF4 : ∀ f, f % 2 = 1 → 3 ≤ f → ordTwistedF4 (2 ^ f) ≠ m
  tits : m ≠ ordTits

theorem card_ne_of_evenLieType
    {m : ℕ} (hm : Excl m) {X : Type} [Group X] (h : EvenLieType X) : Nat.card X ≠ m := by
  obtain ⟨t, n, f, hadm, hmod⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  rcases hmod with ⟨ht, hc⟩ | ⟨-, ht, hce⟩ | ⟨-, ht, hrt⟩ | ⟨-, -, hsz⟩
  · have hcard := CFSG.Timmesfeld.card_statedClassicalModel_two hc
    cases t
    case PSL =>
      obtain ⟨-, -, hn, h22, -⟩ := hadm
      rw [hcard.1 rfl]
      refine hm.psl (n - 1) f (by omega) hf fun h11 => h22 ?_
      simp only [Prod.mk.injEq] at h11
      obtain ⟨h1, rfl⟩ := h11
      simp only [pow_one, Prod.mk.injEq, and_true]
      omega
    case PSU =>
      obtain ⟨-, -, hn, h32⟩ := hadm
      rw [hcard.2.1 rfl]
      refine hm.psu (n - 1) f (by omega) hf fun h21 => h32 ?_
      simp only [Prod.mk.injEq] at h21
      obtain ⟨h1, rfl⟩ := h21
      simp only [pow_one, Prod.mk.injEq, and_true]
      omega
    case PSp =>
      obtain ⟨-, -, hn, h22⟩ := hadm
      rw [hcard.2.2.1 rfl]
      refine hm.psp n f hn hf fun h21 => h22 ?_
      simp only [Prod.mk.injEq] at h21
      obtain ⟨rfl, rfl⟩ := h21
      rfl
    case POmegaOdd => exact absurd rfl hadm.2.2.2
    case POmegaPlus =>
      rw [hcard.2.2.2.1 rfl]
      exact hm.omegaPlus n f hadm.2.2 hf
    case POmegaMinus =>
      rw [hcard.2.2.2.2 rfl]
      exact hm.omegaMinus n f hadm.2.2 hf
    all_goals exact absurd ht (by decide)
  · have hcard := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hce
    cases t
    case G2 =>
      rw [hcard]
      refine hm.g2 f ?_
      have h3 : 3 ≤ 2 ^ f := hadm.2.2.2
      by_contra hlt
      have : f = 1 := by omega
      subst this
      norm_num at h3
    case F4 => rw [hcard]; exact hm.f4 f hf
    case E6 => rw [hcard]; exact hm.e6 f hf
    case E7 => rw [hcard]; exact hm.e7 f hf
    case E8 => rw [hcard]; exact hm.e8 f hf
    case twistedE6 => rw [hcard]; exact hm.e6' f hf
    case trialityD4 => rw [hcard]; exact hm.d4 f hf
    all_goals exact absurd ht (by decide)
  · cases t
    case twistedG2 => exact absurd hadm.2.2.2.1 (by decide)
    case twistedF4 =>
      obtain ⟨k, hk, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel hrt
      rw [hcard]
      exact hm.twistedF4 (2 * k + 1) (by omega) (by omega)
    case Tits =>
      rw [(CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X 2 f hrt).1]
      intro h
      exact hm.tits (by rw [← h]; decide)
    all_goals exact absurd ht (by decide)
  · obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hsz
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hcard : Nat.card X = ordSuzuki (2 ^ f) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hfa, ordSuzuki]
      exact Nat.mul_right_comm _ _ _
    rw [hcard]
    exact hm.sz f (by omega) (by omega)

theorem Excl.of_profile {m a r : ℕ} (hr : Odd r) (hm : m = 2 ^ a * r)
    (hpsl : ∀ n f, 1 ≤ n → 1 ≤ f → (n, f) ≠ (1, 1) → f * (n * (n + 1) / 2) = a →
      ordA n (2 ^ f) ≠ m)
    (hpsu : ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → f * (n * (n + 1) / 2) = a →
      ordTwistedA n (2 ^ f) ≠ m)
    (hpsp : ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → f * (n * n) = a → ordBC n (2 ^ f) ≠ m)
    (hD : ∀ n f, 4 ≤ n → 1 ≤ f → f * (n * (n - 1)) = a →
      ordD n (2 ^ f) ≠ m ∧ ordTwistedD n (2 ^ f) ≠ m)
    (hG2 : ∀ f, 2 ≤ f → f * 6 = a → ordG2 (2 ^ f) ≠ m)
    (hd4 : ∀ f, 1 ≤ f → f * 12 = a → ordTrialityD4 (2 ^ f) ≠ m)
    (hf4 : ∀ f, 1 ≤ f → f * 24 = a → ordF4 (2 ^ f) ≠ m)
    (he6 : ∀ f, 1 ≤ f → f * 36 = a → ordE6 (2 ^ f) ≠ m ∧ ordTwistedE6 (2 ^ f) ≠ m)
    (he7 : ∀ f, 1 ≤ f → f * 63 = a → ordE7 (2 ^ f) ≠ m)
    (he8 : ∀ f, 1 ≤ f → f * 120 = a → ordE8 (2 ^ f) ≠ m)
    (hsz : ∀ f, f % 2 = 1 → 3 ≤ f → f * 2 = a → ordSuzuki (2 ^ f) ≠ m)
    (h2f4 : ∀ f, f % 2 = 1 → 3 ≤ f → f * 12 = a → ordTwistedF4 (2 ^ f) ≠ m)
    (htits : m ≠ ordTits) : Excl m := by
  subst hm
  refine ⟨fun n f hn hf hne => ?_, fun n f hn hf hne => ?_, fun n f hn hf hne => ?_,
    fun n f hn hf => ?_, fun n f hn hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf => ?_,
    fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hodd hf3 => ?_,
    fun f hodd hf3 => ?_, htits⟩
  · by_cases hN : f * (n * (n + 1) / 2) = a
    · exact hpsl n f hn hf hne hN
    · exact (profile_ordA hn hf).ne_of_ne hr hN
  · by_cases hN : f * (n * (n + 1) / 2) = a
    · exact hpsu n f hn hf hne hN
    · exact (profile_ordTwistedA hn hf).ne_of_ne hr hN
  · by_cases hN : f * (n * n) = a
    · exact hpsp n f hn hf hne hN
    · exact (profile_ordBC hf).ne_of_ne hr hN
  · by_cases hN : f * (n * (n - 1)) = a
    · exact (hD n f hn hf hN).1
    · exact (profile_ordD (by omega) hf).ne_of_ne hr hN
  · by_cases hN : f * (n * (n - 1)) = a
    · exact (hD n f hn hf hN).2
    · exact (profile_ordTwistedD (by omega) hf).ne_of_ne hr hN
  · by_cases hN : f * 6 = a
    · exact hG2 f hf hN
    · exact (profile_ordG2 (by omega)).ne_of_ne hr hN
  · by_cases hN : f * 12 = a
    · exact hd4 f hf hN
    · exact (profile_ordTrialityD4 hf).ne_of_ne hr hN
  · by_cases hN : f * 24 = a
    · exact hf4 f hf hN
    · exact (profile_ordF4 hf).ne_of_ne hr hN
  · by_cases hN : f * 36 = a
    · exact (he6 f hf hN).1
    · exact (profile_ordE6 hf).ne_of_ne hr hN
  · by_cases hN : f * 36 = a
    · exact (he6 f hf hN).2
    · exact (profile_ordTwistedE6 hf).ne_of_ne hr hN
  · by_cases hN : f * 63 = a
    · exact he7 f hf hN
    · exact (profile_ordE7 hf).ne_of_ne hr hN
  · by_cases hN : f * 120 = a
    · exact he8 f hf hN
    · exact (profile_ordE8 hf).ne_of_ne hr hN
  · by_cases hN : f * 2 = a
    · exact hsz f hodd hf3 hN
    · exact (profile_ordSuzuki (by omega)).ne_of_ne hr hN
  · by_cases hN : f * 12 = a
    · exact h2f4 f hodd hf3 hN
    · exact (profile_ordTwistedF4 (by omega)).ne_of_ne hr hN

theorem le_tri (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)

theorem psl_of_bounded {m a : ℕ}
    (h : ∀ n ∈ Finset.Icc 1 a, ∀ f ∈ Finset.Icc 1 a, f * (n * (n + 1) / 2) = a →
      (n, f) ≠ (1, 1) → ordA n (2 ^ f) ≠ m) :
    ∀ n f, 1 ≤ n → 1 ≤ f → (n, f) ≠ (1, 1) → f * (n * (n + 1) / 2) = a →
      ordA n (2 ^ f) ≠ m := by
  intro n f hn hf hne hN
  have h1 := le_tri n
  have h2 : n * (n + 1) / 2 ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_left _ hf
  have h3 : f ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact h n (Finset.mem_Icc.mpr ⟨hn, by omega⟩) f (Finset.mem_Icc.mpr ⟨hf, h3⟩) hN hne

theorem psu_of_bounded {m a : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 a, ∀ f ∈ Finset.Icc 1 a, f * (n * (n + 1) / 2) = a →
      (n, f) ≠ (2, 1) → ordTwistedA n (2 ^ f) ≠ m) :
    ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → f * (n * (n + 1) / 2) = a →
      ordTwistedA n (2 ^ f) ≠ m := by
  intro n f hn hf hne hN
  have h1 := le_tri n
  have h2 : n * (n + 1) / 2 ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_left _ hf
  have h3 : f ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact h n (Finset.mem_Icc.mpr ⟨hn, by omega⟩) f (Finset.mem_Icc.mpr ⟨hf, h3⟩) hN hne

theorem psp_of_bounded {m a : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 a, ∀ f ∈ Finset.Icc 1 a, f * (n * n) = a →
      (n, f) ≠ (2, 1) → ordBC n (2 ^ f) ≠ m) :
    ∀ n f, 2 ≤ n → 1 ≤ f → (n, f) ≠ (2, 1) → f * (n * n) = a → ordBC n (2 ^ f) ≠ m := by
  intro n f hn hf hne hN
  have h2 : n * n ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_left _ hf
  have h1 : n ≤ n * n := Nat.le_mul_self n
  have h3 : f ≤ a := by
    rw [← hN]
    exact Nat.le_mul_of_pos_right _ (by nlinarith)
  exact h n (Finset.mem_Icc.mpr ⟨hn, by omega⟩) f (Finset.mem_Icc.mpr ⟨hf, h3⟩) hN hne

theorem omega_of_lt {m a : ℕ} (ha : a < 12) :
    ∀ n f, 4 ≤ n → 1 ≤ f → f * (n * (n - 1)) = a →
      ordD n (2 ^ f) ≠ m ∧ ordTwistedD n (2 ^ f) ≠ m := by
  intro n f hn hf hN
  exfalso
  have : 12 ≤ n * (n - 1) := by
    have : 3 ≤ n - 1 := by omega
    nlinarith
  have : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
  omega

theorem omega_of_odd {m a : ℕ} (ha : a % 2 = 1) :
    ∀ n f, 4 ≤ n → 1 ≤ f → f * (n * (n - 1)) = a →
      ordD n (2 ^ f) ≠ m ∧ ordTwistedD n (2 ^ f) ≠ m := by
  intro n f _ _ hN
  exfalso
  have : Even (f * (n * (n - 1))) := (Nat.even_mul_pred_self n).mul_left f
  rw [hN] at this
  exact Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr ha) this

end CFSG.Quasithin.H13.EvenOrd
