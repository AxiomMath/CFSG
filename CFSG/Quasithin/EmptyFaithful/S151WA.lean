module

public import CFSG.Quasithin.EmptyFaithful.S151ZG
public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.S151ZI
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA

theorem ordA_one_ne_of_factors {m P : ℕ} (hbig : P * (P ^ 2 - 1) < 2 * m)
    (hfac : ∀ p : ℕ, p.Prime → p ∣ 2 * m → p < P) (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ordA 1 p ≠ m := by
  intro h
  have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
  rw [h] at h2
  have hdvd : p ∣ 2 * m := ⟨p ^ 2 - 1, h2⟩
  have hpP := hfac p hp hdvd
  have : p * (p ^ 2 - 1) ≤ P * (P ^ 2 - 1) :=
    Nat.mul_le_mul hpP.le (Nat.sub_le_sub_right (Nat.pow_le_pow_left hpP.le 2) 1)
  omega

theorem lt_of_prime_dvd_of_factors {n P : ℕ} {l : List ℕ} (hn : n ≠ 0)
    (e : Nat.primeFactorsList n = l) (hl : ∀ q ∈ l, q < P) (p : ℕ) (hp : p.Prime) (h : p ∣ n) :
    p < P := by
  have h1 : p ∈ Nat.primeFactorsList n := (Nat.mem_primeFactorsList hn).mpr ⟨hp, h⟩
  rw [e] at h1
  exact hl p h1

theorem not_a38Order_17971200 : ¬ A38Order 17971200 :=
  not_a38Order_of (a := 11) (b := 8775) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 11) hp hp3 ⟨8775, rfl⟩ (by norm_num))

theorem not_a38Order_211341312 : ¬ A38Order 211341312 :=
  not_a38Order_of (a := 12) (b := 51597) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 12) hp hp3 ⟨51597, rfl⟩ (by norm_num))

theorem not_a38Order_604800 : ¬ A38Order 604800 :=
  not_a38Order_of (a := 7) (b := 4725) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 7) hp hp3 ⟨4725, rfl⟩ (by norm_num))

theorem not_a38Order_95040 : ¬ A38Order 95040 :=
  not_a38Order_of (a := 6) (b := 1485) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 6) hp hp3 ⟨1485, rfl⟩ (by norm_num))

theorem not_a38Order_443520 : ¬ A38Order 443520 :=
  not_a38Order_of (a := 7) (b := 3465) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 7) hp hp3 ⟨3465, rfl⟩ (by norm_num))

theorem not_a38Order_244823040 : ¬ A38Order 244823040 :=
  not_a38Order_of (a := 10) (b := 239085) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 10) hp hp3 ⟨239085, rfl⟩ (by norm_num))

theorem not_a38Order_10200960 : ¬ A38Order 10200960 :=
  not_a38Order_of (a := 7) (b := 79695) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (ordA_one_ne_of_factors (m := 10200960) (P := 24) (by norm_num)
      (lt_of_prime_dvd_of_factors (l := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23]) (by norm_num)
        (by norm_num) (by decide)))

theorem not_a38Order_4030387200 : ¬ A38Order 4030387200 :=
  not_a38Order_of (a := 10) (b := 3935925) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (ordA_one_ne_of_factors (m := 4030387200) (P := 18) (by norm_num)
      (lt_of_prime_dvd_of_factors
        (l := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 7, 7, 17]) (by norm_num)
        (by norm_num) (by decide)))

theorem card_quotPCore_of_simple {G : Type} [Group G] {L : Subgroup G} [Finite ↥L]
    (hs : IsSimpleGroup ↥L) (h3 : 3 ∣ Nat.card ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥L := by
  have hb : CFSG.pCore 2 ↥L = ⊥ := pCore_two_eq_bot_of_simple hs h3
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hb).trans
    QuotientGroup.quotientBot).toEquiv

theorem rankTwoSimpleNotA38_holds :
    RankTwoSimpleNotA38 := by
  intro G _ L h hA
  rcases h with h | h | h
  · have hN : Nat.card ↥L = 6048 := psuThreeThreeOrder1522 ↥L h
    have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
    have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity ↥L 3 3 1 h).2
    have hq := card_quotPCore_of_simple hs (by rw [hN]; norm_num)
    rw [hN] at hq
    exact not_a38Order_6048 (hq ▸ a38Order_card hA)
  · obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥L 2 1 h
    have hN : Nat.card ↥L = 17971200 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Schreier.Tits.card_titsD
    have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
    have hs := (CFSG.LieType.Simplicity.fam_tits_simplicity ↥L 2 1 h).2
    have hq := card_quotPCore_of_simple hs (by rw [hN]; norm_num)
    rw [hN] at hq
    exact not_a38Order_17971200 (hq ▸ a38Order_card hA)
  · have hN : Nat.card ↥L = 211341312 := threeD4TwoOrder1522 ↥L h
    have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
    have hs := (CFSG.LieType.Simplicity.fam_3d4_simplicity ↥L 2 1 h).2
    have hq := card_quotPCore_of_simple hs (by rw [hN]; norm_num)
    rw [hN] at hq
    exact not_a38Order_211341312 (hq ▸ a38Order_card hA)

theorem sporadicSixNotA38_holds :
    SporadicSixNotA38 := by
  intro G _ L h hA
  have hc := a38Order_card hA
  rcases h with h | h | h | h | h | h
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J2) = 604800 :=
      CFSG.Sporadic.J2.card_J2
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_604800 hc
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 :=
      CFSG.Sporadic.He.card_He
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_4030387200 hc
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M12) = 95040 :=
      CFSG.Sporadic.Mathieu.card_M12
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_95040 hc
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_443520 hc
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 :=
      card_nativeM23_1522
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_10200960 hc
  · obtain ⟨e⟩ := h
    have hN : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
      CFSG.Sporadic.Mathieu.card_M24
    rw [Nat.card_congr e.toEquiv, hN] at hc
    exact not_a38Order_244823040 hc

end CFSG.Quasithin
