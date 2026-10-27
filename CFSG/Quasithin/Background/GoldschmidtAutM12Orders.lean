module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Core
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.F6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace AutM12Recog

theorem excl_of_card {K : Type} [Group K] [Finite K] {a : ℕ} (ha : 8 ≤ a)
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) : Excl K := by
  intro T _ _ hT Q n N hQN hc _
  obtain ⟨m, hm, hK⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(Q : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card K).factorization 2 = a := by
    rw [hK, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm.not_two_dvd_nat)]
    simp
  rw [h2, Nat.card_congr hQN.some.toEquiv] at h1
  rw [hT.card, h1] at hc
  have h3 : 2 ^ 8 ≤ 2 ^ 7 := by
    calc 2 ^ 8 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      _ ≤ 2 ^ a * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
      _ = 2 ^ 7 := hc.symm
  omega

theorem excl_of_card_two_part {K : Type} [Group K] [Finite K] {m N : ℕ} (hK : Nat.card K = m)
    (hm : ∃ r : ℕ, Odd r ∧ m = 2 ^ N * r) (hN : 8 ≤ N) : Excl K := by
  obtain ⟨r, hr, hmr⟩ := hm
  exact excl_of_card hN ⟨r, hr, hK.trans hmr⟩

theorem excl_of_psl_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSL n 2 f) (hN : 8 ≤ f * ((n - 1) * (n - 1 + 1) / 2)) :
    Excl S := by
  obtain ⟨-, hf, hn, -, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  exact excl_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordA (by omega) hf).two hN

theorem excl_of_psu_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSU n 2 f) (hN : 8 ≤ f * ((n - 1) * (n - 1 + 1) / 2)) :
    Excl S := by
  obtain ⟨-, hf, hn, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
  exact excl_of_card_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (by omega) hf).two hN

theorem excl_of_psp_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) (hN : 8 ≤ f * (n * n)) : Excl S := by
  obtain ⟨-, hf, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  exact excl_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordBC hf).two hN

section Exceptional


theorem excl_of_g2 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : Excl S := by
  have hcard : Nat.card S = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact excl_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordG2 (by omega)).two
    (by omega)

theorem excl_of_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : Excl S := by
  have hcard : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact excl_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two
    (by omega)

theorem excl_of_twistedF4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : Excl S := by
  obtain ⟨k, -, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h
  exact excl_of_card_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (by omega)).two (by omega)

end Exceptional

section Suzuki


theorem excl_of_suzuki {S : Type} [Group S] [Finite S] {f : ℕ} (hf5 : 5 ≤ f)
    (h : SuzukiModel S 2 f) : Excl S := by
  obtain ⟨-, a, -, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  exact excl_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordSuzuki (by omega)).two
    (by omega)

end Suzuki

section Tits


theorem excl_of_tits {S : Type} [Group S] [Finite S] (h : ReeTitsModel S .Tits 2 1) : Excl S := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 h
  have hc : Nat.card S = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact excl_of_card (a := 11) (by norm_num) ⟨8775, by decide, by rw [hc]; norm_num⟩

end Tits

section Sporadic


theorem excl_of_sporadic_large {S : Type} [Group S] [Finite S] {s : TauCeti.SporadicName}
    (hs : s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru)
    (e : S ≃* NativeSporadic.Carrier s) : Excl S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have hc : Nat.card S = 244823040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    exact excl_of_card (a := 10) (by norm_num) ⟨239085, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 86775571046077562880 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    exact excl_of_card (a := 21) (by norm_num)
      ⟨41377816699065, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact excl_of_card (a := 9) (by norm_num) ⟨86625, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 4030387200 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.He.card_He
    exact excl_of_card (a := 10) (by norm_num) ⟨3935925, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 145926144000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    exact excl_of_card (a := 14) (by norm_num) ⟨8906625, by decide, by rw [hc]; norm_num⟩

end Sporadic

end AutM12Recog

end CFSG.Quasithin.F6
