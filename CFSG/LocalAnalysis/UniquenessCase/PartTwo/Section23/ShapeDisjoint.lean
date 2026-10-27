module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.Adapters.LieModelOrders
public import CFSG.GroupTheory.LieTypeOrderBounds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint

theorem not_isL2_of_isSp4 {X : Type} [Group X] {a n : ℕ} (h : IsSp4 X a) : ¬ IsL2 X n := by
  intro hL
  have ha1 : 1 ≤ a := h.admissible.2.1
  have hn1 : 1 ≤ n := hL.admissible.2.1
  have hA : Nat.card X = ordBC 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hB : Nat.card X = ordA 1 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL.card_eq_lieOrd (by norm_num)
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two le_rfl hn1 ha1 (hB.symm.trans hA)

theorem not_isSz_of_isSp4 {X : Type} [Group X] {a n : ℕ} (h : IsSp4 X a) : ¬ IsSz X n := by
  intro hSz
  have h3 : 3 ∣ Nat.card X := by
    rw [show Nat.card X = ordBC 2 (2 ^ a) from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
    exact uc22p21k_three_dvd_ordBC_two a
  exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz h3

theorem not_isL2_of_isU3 {X : Type} [Group X] {a n : ℕ} (h : IsU3 X a) : ¬ IsL2 X n := by
  intro hL
  have ha1 : 1 ≤ a := h.admissible.2.1
  have hn1 : 1 ≤ n := hL.admissible.2.1
  have hA : Nat.card X = ordTwistedA 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hB : Nat.card X = ordA 1 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL.card_eq_lieOrd (by norm_num)
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA le_rfl hn1 (by norm_num) ha1
    (hB.symm.trans hA)

theorem not_isSz_of_isU3 {X : Type} [Group X] {a n : ℕ} (h : IsU3 X a) : ¬ IsSz X n := by
  intro hSz
  have h3 : 3 ∣ Nat.card X := by
    rw [show Nat.card X = ordTwistedA 2 (2 ^ a) from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
    exact uc22p21k_three_dvd_ordTwistedA_two a
  exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz h3

private theorem l2_mul_sq_sub_one_lt_of_le {p Q : ℕ} (hQ8 : 8 ≤ Q) (hle : p ≤ Q + 1) :
    p * (p ^ 2 - 1) < 2 * (Q * (Q ^ 2 - 1)) := by
  have hLHS : p * (p ^ 2 - 1) ≤ (Q + 1) * ((Q + 1) ^ 2 - 1) :=
    Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
  have hRHS : (Q + 1) * ((Q + 1) ^ 2 - 1) < 2 * (Q * (Q ^ 2 - 1)) := by
    have hM : (Q + 1) * ((Q + 1) ^ 2 - 1) = Q * (Q + 1) * (Q + 2) := by
      have h : (Q + 1) ^ 2 - 1 = Q * (Q + 2) := by
        simpa [mul_comm, Nat.add_sub_cancel] using Nat.sq_sub_sq (Q + 1) 1
      rw [h]
      ring
    have hN : 2 * (Q * (Q ^ 2 - 1)) = Q * (Q + 1) * (2 * (Q - 1)) := by
      have h : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq Q 1
      rw [h]
      ring
    rw [hM, hN]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.mul_pos (by omega) (by omega))
    omega
  exact hLHS.trans_lt hRHS

private theorem l2_odd_le_two_pow_add_one {p n : ℕ} (hp5 : 5 < p) (hpprime : p.Prime)
    (hpodd : Odd p) (hn1 : 1 ≤ n)
    (hEq2 : p * (p ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1))) :
    p ≤ 2 ^ n + 1 ∧ 3 ≤ n := by
  have hpodd' : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hpodd
  have hp_dvd_mul : p ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    refine hpodd'.dvd_of_dvd_mul_left ?_
    rw [← hEq2]
    exact dvd_mul_right p (p ^ 2 - 1)
  have hp_dvd_sq : p ∣ (2 ^ n) ^ 2 - 1 :=
    (Nat.Coprime.pow_right n hpodd').dvd_of_dvd_mul_left hp_dvd_mul
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
  rw [hfac] at hp_dvd_sq
  have hpos : 0 < 2 ^ n - 1 := by
    have := Nat.one_lt_two_pow (by omega : n ≠ 0)
    omega
  have hp_le : p ≤ 2 ^ n + 1 := by
    rcases hpprime.dvd_mul.mp hp_dvd_sq with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · exact Nat.le_of_dvd (by positivity) h
  refine ⟨hp_le, ?_⟩
  have hQ5 : 5 ≤ 2 ^ n := by omega
  by_contra h
  have hn2 : n ≤ 2 := by omega
  have hle : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
  norm_num at hle
  omega

theorem not_isL2_of_isL2Odd {X : Type} [Group X] {p n : ℕ} (hp : 5 < p) (h : IsL2Odd X p) :
    ¬ IsL2 X n := by
  intro hL
  have hpprime : p.Prime := h.admissible.1
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hn1 : 1 ≤ n := hL.admissible.2.1
  have hA : Nat.card X = ordA 1 p := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hB : Nat.card X = ordA 1 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL.card_eq_lieOrd (by norm_num)
  have hEq : ordA 1 p = ordA 1 (2 ^ n) := hA.symm.trans hB
  have hP : 2 * ordA 1 p = p * (p ^ 2 - 1) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hpodd
  have hN : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq]
    have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn1)
    rw [hgcd, Nat.div_one]
  have hEq2 : p * (p ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
    rw [← hP, hEq, hN]
  obtain ⟨hp_le, hn3⟩ := l2_odd_le_two_pow_add_one hp hpprime hpodd hn1 hEq2
  have hQ8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hlt := l2_mul_sq_sub_one_lt_of_le hQ8 hp_le
  omega

private theorem finite_of_isJ1 {X : Type} [Group X] (h : IsJ1 X) : Finite X := by
  obtain ⟨e⟩ := h
  exact Finite.of_equiv _ (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm.toEquiv

theorem three_dvd_card_of_isL2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    3 ∣ Nat.card X := by
  rw [show Nat.card X = ordA 1 (2 ^ n) from by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordA (k := 1) (by norm_num)

theorem three_dvd_card_of_isL2Odd {X : Type} [Group X] {p : ℕ} (hp : 3 < p)
    (h : IsL2Odd X p) : 3 ∣ Nat.card X := by
  have hpprime : p.Prime := h.admissible.1
  rw [show Nat.card X = ordA 1 p from by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hnot : ¬ 3 ∣ p := fun h3 => by
    have : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpprime).mp h3).symm
    omega
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
    have hne : p % 3 ≠ 0 := fun h0 => hnot (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hsq : p ^ 2 % 3 = 1 := by
    rcases hmod with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h3p : 3 ∣ p ^ 2 - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by simpa using hsq))
  have h2 := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hpodd
  have h : 3 ∣ 2 * ordA 1 p := by
    rw [h2]
    exact h3p.mul_left p
  exact (by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left h

theorem three_dvd_card_of_isJ1 {X : Type} [Group X] (h : IsJ1 X) :
    3 ∣ Nat.card X := by
  haveI : Finite X := finite_of_isJ1 h
  rw [(kJ1_holds X h).1]
  norm_num

theorem not_isSz_of_isL2Odd {X : Type} [Group X] {p n : ℕ} (hp : 3 < p)
    (h : IsL2Odd X p) : ¬ IsSz X n :=
  fun hSz => CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
    (three_dvd_card_of_isL2Odd hp h)

private theorem j1_prime_eq_seven_or_eleven_or_nineteen {p : ℕ} (hp : p.Prime) (h5 : 5 < p)
    (hdvd : p ∣ 2 ^ 4 * 3 * 5 * 7 * 11 * 19) : p = 7 ∨ p = 11 ∨ p = 19 := by
  rcases hp.dvd_mul.mp hdvd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow h)
            omega
          · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
            omega
        · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
          omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))

theorem not_isL2_of_isJ1 {X : Type} [Group X] {n : ℕ} (h : IsJ1 X) :
    ¬ IsL2 X n := by
  haveI : Finite X := finite_of_isJ1 h
  intro hL2
  have hJcard : Nat.card X = 175560 := (kJ1_holds X h).1
  have hn1 : 1 ≤ n := hL2.admissible.2.1
  have hLcard : Nat.card X = ordA 1 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL2.card_eq_lieOrd (by norm_num)
  have hformula : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq]
    have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn1)
    rw [hgcd, Nat.div_one]
  have hcard : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := hLcard.trans hformula
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [h2]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have heq : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 2 ^ 3 * 21945 := by
    rw [← hcard, hJcard]
    norm_num
  have hn3 : n = 3 :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd (by norm_num) heq
  subst hn3
  rw [hcard] at hJcard
  norm_num at hJcard

theorem not_isSz_of_isJ1 {X : Type} [Group X] {n : ℕ} (h : IsJ1 X) :
    ¬ IsSz X n := by
  haveI : Finite X := finite_of_isJ1 h
  intro hSz
  exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
    (three_dvd_card_of_isJ1 h)

theorem not_isL2Odd_of_isJ1 {X : Type} [Group X] {p : ℕ} (hp : 5 < p)
    (h : IsJ1 X) : ¬ IsL2Odd X p := by
  haveI : Finite X := finite_of_isJ1 h
  intro hL
  have hpprime : p.Prime := hL.admissible.1
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hcardL : Nat.card X = ordA 1 p := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL.card_eq_lieOrd (by norm_num)
  have hcardJ : Nat.card X = 175560 := (kJ1_holds X h).1
  have hEq : ordA 1 p = 175560 := hcardL.symm.trans hcardJ
  have h2 := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hpodd
  have h2eq : p * (p ^ 2 - 1) = 351120 := by
    calc p * (p ^ 2 - 1) = 2 * ordA 1 p := h2.symm
      _ = 2 * 175560 := by rw [hEq]
      _ = 351120 := by norm_num
  have hfac : 351120 = 2 ^ 4 * 3 * 5 * 7 * 11 * 19 := by norm_num
  have hp_dvd : p ∣ 2 ^ 4 * 3 * 5 * 7 * 11 * 19 := by
    rw [← hfac]
    exact ⟨p ^ 2 - 1, h2eq.symm⟩
  rcases j1_prime_eq_seven_or_eleven_or_nineteen hpprime (by omega) hp_dvd with rfl | rfl | rfl
  · exact (by decide : ordA 1 7 ≠ 175560) hEq
  · exact (by decide : ordA 1 11 ≠ 175560) hEq
  · exact (by decide : ordA 1 19 ≠ 175560) hEq

private theorem sixteen_dvd_card_of_isSp4 {X : Type} [Group X] {n : ℕ} (h : IsSp4 X n) :
    16 ∣ Nat.card X := by
  have hcard : Nat.card X = ordBC 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hn1 : 1 ≤ n := h.admissible.2.1
  obtain ⟨r, -, hr⟩ := CFSG.GroupTheory.two_part_ordBC_two (e := n) hn1
  rw [hcard, hr]
  exact (pow_dvd_pow 2 (show 4 ≤ n * 4 by omega)).mul_right r

private theorem sixteen_dvd_card_of_isSU3 {X : Type} [Group X] {n : ℕ} (h : IsSU3 X n)
    (hZ : Subgroup.center X = ⊥) : 16 ∣ Nat.card X := by
  have hquot : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := uc22p21k_card_quot_center hZ
  have hcard : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.2.card_eq_lieOrd (by norm_num)
  have hn1 : 1 ≤ n := h.2.admissible.2.1
  have hn2 : 2 ≤ n := by
    by_contra hn
    have hn1' : n = 1 := by omega
    exact h.2.admissible.2.2.2 (by rw [hn1']; norm_num)
  obtain ⟨r, -, hr⟩ := CFSG.GroupTheory.two_part_ordTwistedA_two (e := n) hn1
  have h16 : 16 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [hcard, hr]
    exact (pow_dvd_pow 2 (show 4 ≤ n * 3 by omega)).mul_right r
  rwa [hquot] at h16

theorem j1NotSp4SU3 : J1NotSp4SU3 := by
  intro X _ h
  haveI : Finite X := finite_of_isJ1 h
  have hdata := kJ1_holds X h
  have hcard : Nat.card X = 175560 := hdata.1
  haveI : IsSimpleGroup X := hdata.2.1
  have hprime : ¬ (Nat.card X).Prime := by
    rw [hcard]
    norm_num
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hZ | hZ
    · exact hZ
    · exfalso
      have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b) a
      letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
      exact hprime (Group.is_simple_iff_prime_card.mp inferInstance)
  refine ⟨hZ, ?_, ?_⟩
  · intro n hsp
    have h16 := sixteen_dvd_card_of_isSp4 hsp
    rw [hcard] at h16
    norm_num at h16
  · intro n hsu
    have h16 := sixteen_dvd_card_of_isSU3 hsu hZ
    rw [hcard] at h16
    norm_num at h16

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
