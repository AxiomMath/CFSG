module

public import CFSG.RankThree.GF2n.Smith81.InspKFacts
public import CFSG.RankThree.GF2n.Smith81.InspKStatements
public import CFSG.RankThree.GF2n.Smith81.InspLinArith
public import CFSG.RankThree.GF2n.Smith81.InspPpd
public import CFSG.RankThree.GF2n.Smith81.TiRecognition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (ordSL)

theorem pow_sub_one_dvd_ordSL {n e q : ℕ} (he : 2 ≤ e) (hen : e ≤ n) : q ^ e - 1 ∣ ordSL n q :=
  Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨he, hen⟩)) _

theorem pow_dvd_ordSL (n q : ℕ) : q ^ (n * (n - 1) / 2) ∣ ordSL n q := Dvd.intro _ rfl

theorem le_of_two_pow_dvd_of_profile {m N a : ℕ} {Z : ℕ → Prop} (h : Profile m N Z)
    (hd : 2 ^ a ∣ m) : a ≤ N := by
  obtain ⟨r, hr, rfl⟩ := h.two
  have hcop : Nat.Coprime (2 ^ a) r := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hr)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hd)

theorem factorization_two_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) :
    m.factorization 2 = N := by
  obtain ⟨r, hr, hm⟩ := h.two
  exact factorization_two_eq_of_odd hm hr

theorem exists_ppd_dvd_ordSL {n e f : ℕ} (hf : 1 ≤ f) (he : 2 ≤ e) (hen : e ≤ n)
    (h6 : e * f ≠ 6) : ∃ p, IsPrimitivePrimeDivisor p (e * f) ∧ p ∣ ordSL n (2 ^ f) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := e * f) (by nlinarith) h6
  refine ⟨p, hp, Dvd.dvd.trans ?_ (pow_sub_one_dvd_ordSL he hen)⟩
  rw [← pow_mul, mul_comm f e]
  exact hp.dvd

theorem factorization_two_lt (f : ℕ) (hf : 1 ≤ f) : f.factorization 2 < f := by
  have h1 : 2 ^ f.factorization 2 ≤ f := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd f 2)
  have h2 : f.factorization 2 < 2 ^ f.factorization 2 := Nat.lt_two_pow_self
  omega

theorem not_mul_dvd_mul_of_not_dvd {e f a : ℕ} (hf : 0 < f) (h : ¬ e ∣ a) : ¬ e * f ∣ f * a :=
  fun h' => h (dvd_of_mul_dvd_mul_left' hf h')

theorem odd_dvd_of_mul_dvd_two_mul {e f i : ℕ} (hf : 0 < f) (he : Odd e)
    (h : e * f ∣ f * (2 * i)) : e ∣ i :=
  odd_dvd_of_dvd_two_mul he (dvd_of_mul_dvd_mul_left' hf h)

theorem linCore (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2) (hKCO : KCOmegaStatement2)
    {Y : Type} [Group Y] [Finite Y] {D : Set Y} (hH : Hyp Y D) {t : StatedLieTag} {k f : ℕ}
    (hf : 2 ≤ f) (htag : TimmesfeldTag t k f) (hL : LieModel Y t k 2 f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) {n : ℕ} (hn : 4 ≤ n) {z : Y}
    (hz : z ∈ D)
    (hQ : (2 ^ f) ^ (2 * n + 1) ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer ({z} : Set Y))))
    (hP : (2 ^ f) ^ (2 * n + 1) * ordSL n (2 ^ f) ∣
      Nat.card (Subgroup.centralizer ({z} : Set Y)))
    (hup : (Nat.card Y).factorization 2 ≤ f * (2 * n + 1) + f * (n * (n - 1) / 2) +
      2 * f.factorization 2 + 2) :
    t = .PSL ∧ k = n + 2 := by
  have hf1 : 1 ≤ f := by omega
  have hf0 : 0 < f := by omega
  have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hPY : (2 ^ f) ^ (2 * n + 1) * ordSL n (2 ^ f) ∣ Nat.card Y :=
    hP.trans (Subgroup.card_subgroup_dvd_card _)
  have h2lo : 2 ^ (f * (2 * n + 1) + f * (n * (n - 1) / 2)) ∣ Nat.card Y := by
    rw [pow_add, pow_mul, pow_mul]
    exact (mul_dvd_mul_left _ (pow_dvd_ordSL n (2 ^ f))).trans hPY
  have hSL : ordSL n (2 ^ f) ∣ Nat.card Y := (Dvd.intro_left _ rfl).trans hPY
  have hppd : ∀ e, 2 ≤ e → e ≤ n → e * f ≠ 6 →
      ∃ p, IsPrimitivePrimeDivisor p (e * f) ∧ p ∣ Nat.card Y := by
    intro e he hen h6
    obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordSL hf1 he hen h6
    exact ⟨p, hp, hpd.trans hSL⟩
  have hv := factorization_two_lt f hf1
  have hev : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have hS : (n + 1) * (n + 2) = 2 * (2 * n + 1) + n * (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hwin : ∀ {N : ℕ} {Zp : ℕ → Prop}, Profile (Nat.card Y) (f * N) Zp →
      (n + 1) * (n + 2) ≤ 2 * N ∧ 2 * N ≤ (n + 1) * (n + 2) + 4 := by
    intro N Zp hpr
    have hlo := le_of_two_pow_dvd_of_profile hpr h2lo
    have hhi := hup
    rw [factorization_two_of_profile hpr] at hhi
    have h1 : 2 * n + 1 + n * (n - 1) / 2 ≤ N := by
      rw [← mul_add] at hlo
      exact Nat.le_of_mul_le_mul_left hlo hf0
    have h2 : N ≤ 2 * n + 1 + n * (n - 1) / 2 + 2 := by
      by_contra hc
      push Not at hc
      have h3 : f * (2 * n + 1 + n * (n - 1) / 2 + 3) ≤ f * N := Nat.mul_le_mul_left _ hc
      nlinarith
    constructor <;> nlinarith
  have h6case : ∀ e, 3 ≤ e → n - 1 ≤ e → e * f = 6 → f = 2 ∧ e = 3 ∧ n = 4 := by
    intro e he3 he1 h6
    have h3f : 3 * f ≤ e * f := Nat.mul_le_mul_right f he3
    have hf2 : f = 2 := by omega
    subst hf2
    omega
  rcases htag with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨ht, hk⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, ht⟩
  ·
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
    have hpr : Profile (Nat.card Y) (f * ((k - 1) * (k - 1 + 1) / 2)) (zA (k - 1) f) := by
      rw [hcard]
      exact profile_ordA (by omega) hf1
    obtain ⟨-, hhi⟩ := hwin hpr
    have hO := hK2L Y D k f hH hk hf hL hroot z hz
    have hw : 2 * n + 1 ≤ 2 * k - 3 := (Nat.pow_le_pow_iff_right hq1).mp (hQ.trans hO)
    refine ⟨rfl, lin_psl_arith hn (by omega) ?_⟩
    have hev' : 2 * ((k - 1) * (k - 1 + 1) / 2) = (k - 1) * (k - 1 + 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k - 1))
    have hkk : (k - 1) * (k - 1 + 1) = (k - 1) * k := by
      congr 1
      omega
    rw [hkk] at hev'
    omega
  ·
    exfalso
    have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.1 rfl
    have hpr : Profile (Nat.card Y) (f * (k * k)) (zBC k f) := by
      rw [hcard]
      exact profile_ordBC hf1
    obtain ⟨hlo, hhi⟩ := hwin hpr
    rcases hK2S Y D k f hH hk hf hL hroot z hz with hO | ⟨hO, hCd⟩
    · have hw : 2 * n + 1 ≤ 2 * k - 1 := (Nat.pow_le_pow_iff_right hq1).mp (hQ.trans hO)
      exact lin_psp_arith_trans hn (by omega) hhi
    · obtain ⟨e, heo, he1, hen, he3⟩ := exists_odd_near n hn
      have hPC := hP.trans hCd
      by_cases h6 : e * f = 6
      · obtain ⟨rfl, rfl, rfl⟩ := h6case e he3 he1 h6
        have hk4 : k = 4 := by nlinarith
        subst hk4
        have h7 : 7 ∣ (2 ^ 2) ^ (2 * 4 + 1) * ordSL 4 (2 ^ 2) := by
          unfold ordSL
          decide
        have h7' := h7.trans hPC
        revert h7'
        unfold ordBC
        decide
      · obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordSL hf1 (by omega) hen h6
        have hE : 0 < e * f := by positivity
        have hpC : p ∣ (2 ^ f) ^ (4 * k - 5) * (ordBC 1 (2 ^ f) * ordBC (k - 2) (2 ^ f)) := by
          rw [← mul_assoc]
          exact hpd.trans ((Dvd.intro_left _ rfl).trans hPC)
        rcases hp.prime.dvd_mul.mp (ppd_dvd_of_dvd_two_pow_mul hp hE hpC) with h1 | h1
        · obtain ⟨i, hi1, hi2, hei⟩ := ppd_of_dvd_ordBC hp hE hf1 h1
          have := Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 heo hei)
          omega
        · obtain ⟨i, hi1, hi2, hei⟩ := ppd_of_dvd_ordBC hp hE hf1 h1
          have := Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 heo hei)
          exact lin_psp_arith_long hn he1 (by omega) hhi
  ·
    exfalso
    obtain ⟨e, heo, he1, hen, he3⟩ := exists_odd_near n hn
    have key : ∀ {Zp : ℕ → Prop}, Profile (Nat.card Y) (f * (k * (k - 1))) Zp →
        (∀ p, IsPrimitivePrimeDivisor p (e * f) → p ∣ Nat.card Y → e ≤ k) → n = 6 ∧ k = 6 := by
      intro Zp hpr hZk
      obtain ⟨hlo, hhi⟩ := hwin hpr
      by_cases h6 : e * f = 6
      · obtain ⟨rfl, rfl, rfl⟩ := h6case e he3 he1 h6
        have hk4 : k ≤ 5 := by
          by_contra hc
          push Not at hc
          have : 6 * 5 ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
          omega
        interval_cases k <;> omega
      · obtain ⟨p, hp, hpY⟩ := hppd e (by omega) hen h6
        exact lin_omega_arith hn he1 hen heo (hZk p hp hpY) hlo hhi
    have hKC := fun (hk6 : k = 6) => hk6 ▸ hKCO Y D k f hH (by omega) hf hroot
    obtain ⟨p', hp', hpd'⟩ := exists_ppd_dvd_ordSL (n := 6) (e := 5) hf1 (by norm_num)
      (by norm_num) (by omega)
    have hE5 : 0 < 5 * f := by positivity
    have hPC : ∀ c : ℕ, n = 6 → Nat.card (Subgroup.centralizer ({z} : Set Y)) ∣
        (2 ^ f) ^ (4 * 6 - 7) * ordBC 1 (2 ^ f) * c → p' ∣ ordBC 1 (2 ^ f) * c := by
      intro c hn6 hc
      subst hn6
      have h1 : p' ∣ (2 ^ f) ^ (4 * 6 - 7) * (ordBC 1 (2 ^ f) * c) := by
        rw [← mul_assoc]
        exact hpd'.trans ((Dvd.intro_left _ rfl).trans (hP.trans hc))
      exact ppd_dvd_of_dvd_two_pow_mul hp' hE5 h1
    have hBC : ¬ p' ∣ ordBC 1 (2 ^ f) := by
      intro h1
      obtain ⟨i, hi1, hi2, hei⟩ := ppd_of_dvd_ordBC hp' hE5 hf1 h1
      have := Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 (by decide) hei)
      omega
    rcases ht with rfl | rfl
    · have hcard := (card_statedClassicalModel_two
        (hL.statedClassicalModel (by decide))).2.2.2.1 rfl
      obtain ⟨hn6, hk6⟩ := key (Zp := zD k f) (by rw [hcard]; exact profile_ordD (by omega) hf1)
        (fun p hp hpY => by
          rw [hcard] at hpY
          rcases ppd_of_dvd_ordD hp (by positivity) hf1 (by omega) hpY with hdk | ⟨i, hi1, hi2, hdi⟩
          · exact Nat.le_of_dvd (by omega) (dvd_of_mul_dvd_mul_left' hf0 hdk)
          · exact (Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 heo hdi)).trans
              (by omega))
      subst hk6
      have h1 := hPC _ hn6 (((hKC rfl).1 hL) z hz)
      rcases hp'.prime.dvd_mul.mp h1 with h1 | h1
      · exact hBC h1
      · rcases ppd_of_dvd_ordD hp' hE5 hf1 (by norm_num) h1 with hd | ⟨i, hi1, hi2, hdi⟩
        · exact not_mul_dvd_mul_of_not_dvd hf0 (by norm_num) hd
        · have := Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 (by decide) hdi)
          omega
    · have hcard := (card_statedClassicalModel_two
        (hL.statedClassicalModel (by decide))).2.2.2.2 rfl
      obtain ⟨hn6, hk6⟩ := key (Zp := z2D k f)
        (by rw [hcard]; exact profile_ordTwistedD (by omega) hf1)
        (fun p hp hpY => by
          rw [hcard] at hpY
          rcases ppd_of_dvd_ordTwistedD hp (by positivity) hf1 (by omega) hpY with
            ⟨hdk, hndk⟩ | ⟨i, hi1, hi2, hdi⟩
          · exfalso
            have hek : e ∣ k := odd_dvd_of_dvd_two_mul heo
              (dvd_of_mul_dvd_mul_left' hf0 (by rwa [mul_left_comm] at hdk))
            exact hndk (by rw [mul_comm e f]; exact Nat.mul_dvd_mul_left f hek)
          · exact (Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 heo hdi)).trans
              (by omega))
      subst hk6
      have h1 := hPC _ hn6 (((hKC rfl).2 hL) z hz)
      rcases hp'.prime.dvd_mul.mp h1 with h1 | h1
      · exact hBC h1
      · rcases ppd_of_dvd_ordTwistedD hp' hE5 hf1 (by norm_num) h1 with
          ⟨hd, -⟩ | ⟨i, hi1, hi2, hdi⟩
        · have := odd_dvd_of_dvd_two_mul (by decide : Odd 5)
            (dvd_of_mul_dvd_mul_left' hf0 (by rwa [mul_left_comm] at hd))
          norm_num at this
        · have := Nat.le_of_dvd (by omega) (odd_dvd_of_mul_dvd_two_mul hf0 (by decide) hdi)
          omega
  ·
    exfalso
    have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by decide))
    have hpr : Profile (Nat.card Y) (f * 6) (zG2 f) := by
      rw [hcard]
      exact profile_ordG2 hf1
    obtain ⟨hlo, -⟩ := hwin hpr
    nlinarith
  ·
    exfalso
    have hexc : ∀ {N : ℕ} {Zp : ℕ → Prop}, Profile (Nat.card Y) (f * N) Zp →
        (N = 6 ∨ N = 12 ∨ N = 24 ∨ N = 36 ∨ N = 63 ∨ N = 120) →
        (N = 36 → ∀ p, IsPrimitivePrimeDivisor p (7 * f) → p ∣ Nat.card Y → False) →
        (N = 120 → ∀ p, IsPrimitivePrimeDivisor p (13 * f) → p ∣ Nat.card Y → False) →
        False := by
      intro N Zp hpr hN h7 h13
      obtain ⟨hlo, hhi⟩ := hwin hpr
      rcases lin_exc_arith hn hN hlo hhi with ⟨hN36, rfl⟩ | ⟨hN120, rfl⟩
      · obtain ⟨p, hp, hpY⟩ := hppd 7 (by norm_num) le_rfl (by omega)
        exact h7 hN36 p hp hpY
      · obtain ⟨p, hp, hpY⟩ := hppd 13 (by norm_num) (by norm_num) (by omega)
        exact h13 hN120 p hp hpY
    have hzl : ∀ {e : ℕ} {L : List ℕ}, (∀ a ∈ L, ¬ e ∣ a) → (∃ a ∈ L, e * f ∣ f * a) → False := by
      intro e L hL' ⟨a, ha, hda⟩
      exact hL' a ha (dvd_of_mul_dvd_mul_left' hf0 hda)
    have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hexc (Zp := zD4 f) (by rw [hcard]; exact profile_ordTrialityD4 hf1) (by norm_num)
        (fun h => by omega) (fun h => by omega)
    · exact hexc (Zp := zF4 f) (by rw [hcard]; exact profile_ordF4 hf1) (by norm_num)
        (fun h => by omega) (fun h => by omega)
    · exact hexc (Zp := zE6 f) (by rw [hcard]; exact profile_ordE6 hf1) (by norm_num)
        (fun _ p hp hpY => by
          rw [hcard] at hpY
          exact hzl (by decide) (ppd_of_dvd_ordE6 hp (by positivity) hpY))
        (fun h => by omega)
    · exact hexc (Zp := z2E6 f) (by rw [hcard]; exact profile_ordTwistedE6 hf1) (by norm_num)
        (fun _ p hp hpY => by
          rw [hcard] at hpY
          rcases ppd_of_dvd_ordTwistedE6 hp (by positivity) hpY with h | ⟨a, ha, h, -⟩
          · exact hzl (by decide) h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl
            · rw [show 2 * (f * 9) = f * 18 by ring] at h
              exact not_mul_dvd_mul_of_not_dvd hf0 (by norm_num : ¬ (7 : ℕ) ∣ 18) h
            · rw [show 2 * (f * 5) = f * 10 by ring] at h
              exact not_mul_dvd_mul_of_not_dvd hf0 (by norm_num : ¬ (7 : ℕ) ∣ 10) h)
        (fun h => by omega)
    · exact hexc (Zp := zE7 f) (by rw [hcard]; exact profile_ordE7 hf1) (by norm_num)
        (fun h => by omega) (fun h => by omega)
    · exact hexc (Zp := zE8 f) (by rw [hcard]; exact profile_ordE8 hf1) (by norm_num)
        (fun h => by omega)
        (fun _ p hp hpY => by
          rw [hcard] at hpY
          exact hzl (by decide) (ppd_of_dvd_ordE8 hp (by positivity) hpY))

end CFSG.RankThree.GF2n.Smith81.Insp
