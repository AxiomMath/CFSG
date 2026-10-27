module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Quasithin.MS93.FFOrders
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.Quasithin.Background.F918Z4c1Ppd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SeitzReduction
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open scoped Pointwise

section Certified


private theorem lt_ordTwistedF4_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    6048 < ordTwistedF4 (2 ^ n) := by
  set q := 2 ^ n
  have hq8 : 8 ≤ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq2 : 2 ≤ q := by omega
  have h12 : 6048 < q ^ 12 := by
    calc 6048 < 8 ^ 12 := by norm_num
      _ ≤ q ^ 12 := Nat.pow_le_pow_left hq8 12
  have h6 : 0 < q ^ 6 + 1 := by positivity
  have h4 : 0 < q ^ 4 - 1 := by
    have hq4 : 2 ≤ q ^ 4 := by
      have h := Nat.pow_le_pow_left hq2 4
      norm_num at h
      omega
    omega
  have h3 : 0 < q ^ 3 + 1 := by positivity
  have h1 : 0 < q - 1 := by omega
  calc 6048 < q ^ 12 := h12
    _ ≤ q ^ 12 * (q ^ 6 + 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) := Nat.le_mul_of_pos_right _ h4
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) :=
        Nat.le_mul_of_pos_right _ h3
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) :=
        Nat.le_mul_of_pos_right _ h1
    _ = ordTwistedF4 q := rfl

private theorem lt_ordTrialityD4_of_6048 {n : ℕ} (hn : 1 ≤ n) :
    6048 < ordTrialityD4 (2 ^ n) := by
  set q := 2 ^ n
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h12 : 6048 < q ^ 12 * (q ^ 8 + q ^ 4 + 1) := by
    have hq12 : 2 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq2 12
    have hq8 : 2 ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hq2 8
    have hq4 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
    have h8 : 273 ≤ q ^ 8 + q ^ 4 + 1 := by norm_num at hq8 hq4; omega
    calc 6048 < 2 ^ 12 * 273 := by norm_num
      _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) := Nat.mul_le_mul hq12 h8
  have h8 : 0 < q ^ 8 + q ^ 4 + 1 := by positivity
  have h6 : 0 < q ^ 6 - 1 := by
    have hq6 : 2 ≤ q ^ 6 := by
      have h := Nat.pow_le_pow_left hq2 6
      norm_num at h
      omega
    omega
  have h2 : 0 < q ^ 2 - 1 := by
    have hq2' : 2 ≤ q ^ 2 := by
      have h := Nat.pow_le_pow_left hq2 2
      norm_num at h
      omega
    omega
  calc 6048 < q ^ 12 * (q ^ 8 + q ^ 4 + 1) := h12
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
        Nat.le_mul_of_pos_right _ h2
    _ = ordTrialityD4 q := rfl



private theorem two_pow_thirty_mul_lt_factorial_div (f : ℕ) (hf : 1 ≤ f) :
    2 ^ (30 * f) < Nat.factorial (12 * f + 1) / 2 := by
  induction f with
  | zero => omega
  | succ f ih =>
    rcases Nat.eq_zero_or_pos f with rfl | hfpos
    · norm_num
    · have hf1 : 1 ≤ f := hfpos
      have ih' := ih hf1
      have h2dvd : 2 ∣ Nat.factorial (12 * f + 1) := Nat.dvd_factorial (by norm_num) (by omega)
      have h1 : 2 ^ (30 * f) * 2 < Nat.factorial (12 * f + 1) := by
        have h := Nat.mul_lt_mul_of_pos_right ih' (by norm_num : 0 < 2)
        rwa [Nat.div_mul_cancel h2dvd] at h
      have hstep : Nat.factorial (12 * f + 1) * (12 * f + 2) ^ 12 ≤
          Nat.factorial (12 * (f + 1) + 1) := by
        have h := Nat.factorial_mul_pow_le_factorial (m := 12 * f + 1) (n := 12)
        rw [show 12 * (f + 1) + 1 = 12 * f + 1 + 12 by ring,
          show 12 * f + 2 = 12 * f + 1 + 1 by ring]
        exact h
      have hbase : (2 : ℕ) ^ 30 < (12 * f + 2) ^ 12 := by
        have h13 : (13 : ℕ) ^ 12 ≤ (12 * f + 2) ^ 12 :=
          Nat.pow_le_pow_left (by omega) 12
        exact lt_of_lt_of_le (by norm_num : (2 : ℕ) ^ 30 < 13 ^ 12) h13
      have hbig : 2 ^ (30 * (f + 1) + 1) < Nat.factorial (12 * (f + 1) + 1) := by
        calc 2 ^ (30 * (f + 1) + 1) = 2 ^ (30 * f + 1) * 2 ^ 30 := by
              rw [show 30 * (f + 1) + 1 = (30 * f + 1) + 30 by omega, pow_add]
          _ = (2 ^ (30 * f) * 2) * 2 ^ 30 := by rw [pow_succ]
          _ < Nat.factorial (12 * f + 1) * 2 ^ 30 := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
          _ < Nat.factorial (12 * f + 1) * (12 * f + 2) ^ 12 :=
              Nat.mul_lt_mul_of_pos_left hbase (Nat.factorial_pos _)
          _ ≤ Nat.factorial (12 * (f + 1) + 1) := hstep
      refine (Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)).mpr ?_
      rw [show 2 ^ (30 * (f + 1)) * 2 = 2 ^ (30 * (f + 1) + 1) from
        (pow_succ 2 (30 * (f + 1))).symm]
      have h2dvd' : 2 ∣ Nat.factorial (12 * (f + 1) + 1) :=
        Nat.dvd_factorial (by norm_num) (by omega)
      obtain ⟨k, hk⟩ := h2dvd'
      rw [hk] at hbig ⊢
      rw [pow_succ] at hbig
      omega

private theorem ordTwistedF4_le_two_pow {f : ℕ} (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ f) ≤ 2 ^ (30 * f) := by
  set q := 2 ^ f
  have hq : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqpos : 0 < q := by omega
  have h6 : q ^ 6 + 1 ≤ q ^ 7 := by nlinarith [pow_pos hqpos 6]
  have h4 : q ^ 4 - 1 ≤ q ^ 4 := by
    have : 1 ≤ q ^ 4 := Nat.one_le_pow 4 q (by omega)
    omega
  have h3 : q ^ 3 + 1 ≤ q ^ 4 := by nlinarith [pow_pos hqpos 3]
  have h1 : q - 1 ≤ q := by omega
  have hAB : (q ^ 6 + 1) * (q ^ 4 - 1) ≤ q ^ 7 * q ^ 4 :=
    Nat.mul_le_mul h6 h4
  have hABC : (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 :=
    Nat.mul_le_mul hAB h3
  have hABCD : (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤
      q ^ 7 * q ^ 4 * q ^ 4 * q := Nat.mul_le_mul hABC h1
  calc ordTwistedF4 q = q ^ 12 * ((q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)) := by
        unfold ordTwistedF4
        ring
    _ ≤ q ^ 12 * (q ^ 7 * q ^ 4 * q ^ 4 * q) := Nat.mul_le_mul_left _ hABCD
    _ = q ^ 28 := by ring
    _ = 2 ^ (28 * f) := by rw [show q = 2 ^ f from rfl, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (30 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem ordTrialityD4_le_two_pow {f : ℕ} (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ f) ≤ 2 ^ (30 * f) := by
  set q := 2 ^ f
  have hq : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqpos : 0 < q := by omega
  have h8 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
    rcases eq_or_lt_of_le hq with hq2 | hq3
    · have hqeq : q = 2 := hq2.symm
      rw [hqeq]
      norm_num
    · have hq3' : 3 ≤ q := hq3
      have h48 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      have h18 : 1 ≤ q ^ 8 := Nat.one_le_pow 8 q (by omega)
      have h3q : 3 * q ^ 8 ≤ q ^ 9 := by
        rw [show q ^ 9 = q * q ^ 8 by ring]
        exact Nat.mul_le_mul_right _ hq3'
      nlinarith
  have h6 : q ^ 6 - 1 ≤ q ^ 6 := by
    have : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q (by omega)
    omega
  have h2 : q ^ 2 - 1 ≤ q ^ 2 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
    omega
  have hAB : (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) ≤ q ^ 9 * q ^ 6 :=
    Nat.mul_le_mul h8 h6
  have hABC : (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤
      q ^ 9 * q ^ 6 * q ^ 2 := Nat.mul_le_mul hAB h2
  calc ordTrialityD4 q = q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) := by
        unfold ordTrialityD4
        ring
    _ ≤ q ^ 12 * (q ^ 9 * q ^ 6 * q ^ 2) := Nat.mul_le_mul_left _ hABC
    _ = q ^ 29 := by ring
    _ = 2 ^ (29 * f) := by rw [show q = 2 ^ f from rfl, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (30 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem two_le_of_eq_alt_card {M m : ℕ} (hM : 1 < M)
    (h : M = Nat.card (alternatingGroup (Fin m))) : 2 ≤ m := by
  by_contra hm
  have hmle : m ≤ 1 := by omega
  have hcard_le : Nat.card (alternatingGroup (Fin m)) ≤ 1 := by
    calc Nat.card (alternatingGroup (Fin m)) ≤ Nat.card (Equiv.Perm (Fin m)) :=
          Subgroup.card_le_card_group (alternatingGroup (Fin m))
      _ = Nat.factorial (Nat.card (Fin m)) := by rw [Nat.card_perm]
      _ = Nat.factorial m := by rw [Nat.card_fin]
      _ = 1 := by interval_cases m <;> norm_num
  have hpos : 1 ≤ Nat.card (alternatingGroup (Fin m)) := Nat.card_pos
  have hcard1 : Nat.card (alternatingGroup (Fin m)) = 1 := le_antisymm hcard_le hpos
  rw [hcard1] at h
  omega

private theorem one_lt_ordTwistedF4 {f : ℕ} (hf : 1 ≤ f) :
    1 < ordTwistedF4 (2 ^ f) := by
  rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | hf3
  · norm_num [ordTwistedF4]
  · norm_num [ordTwistedF4]
  · exact lt_trans (by norm_num : (1 : ℕ) < 6048) (lt_ordTwistedF4_of_three_le hf3)

private theorem one_lt_ordTrialityD4_of_6048 {f : ℕ} (hf : 1 ≤ f) :
    1 < ordTrialityD4 (2 ^ f) := by
  exact lt_trans (by norm_num : (1 : ℕ) < 6048) (lt_ordTrialityD4_of_6048 hf)

private theorem ordTwistedF4_ne_card_alternating {f m : ℕ} (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ f) ≠ Nat.card (alternatingGroup (Fin m)) := by
  intro h
  have hm2 : 2 ≤ m := two_le_of_eq_alt_card (one_lt_ordTwistedF4 hf) h
  haveI : Nontrivial (Fin m) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro hcon
      exact Nat.zero_ne_one (congrArg Fin.val hcon)⟩
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  obtain ⟨p, hprim⟩ :=
    exists_isPrimitivePrimeDivisor (k := 12 * f) (by omega) (by omega)
  have hp : p.Prime := hprim.prime
  have hpord : p ∣ ordTwistedF4 (2 ^ f) := by
    have hprof := Timmesfeld.Orders.profile_ordTwistedF4 hf
    have hnot : ¬ 12 * f ∣ f * 6 := by
      intro hdvd
      have h26 : 2 ∣ 1 := by
        have h' : f * 12 ∣ f * 6 := by simpa [mul_comm] using hdvd
        have h2 : 12 ∣ 6 := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f) h'
        norm_num at h2
      norm_num at h26
    exact (hprof.prim p (12 * f) hprim (by omega)).2
      (Or.inl ⟨by simpa [show 2 * (f * 6) = 12 * f by ring] using dvd_rfl, hnot⟩)
  have hp2 : p ≠ 2 := hprim.ne_two (by omega)
  have hpdvd : p ∣ Nat.factorial m := by
    have hpdiv : p ∣ Nat.factorial m / 2 := h ▸ hpord
    have hmul : 2 * (Nat.factorial m / 2) = Nat.factorial m :=
      Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hm2)
    rw [← hmul]
    exact dvd_mul_of_dvd_right hpdiv 2
  have hpm : p ≤ m := (Nat.Prime.dvd_factorial hp).1 hpdvd
  have hpge : 12 * f + 1 ≤ p := by
    have hord : orderOf (2 : ZMod p) = 12 * f :=
      CFSG.Quasithin.orderOf_two_eq_of_isPrimitivePrimeDivisor hprim (by omega)
    haveI : Fact p.Prime := ⟨hp⟩
    have hdvd : 12 * f ∣ p - 1 := by
      rw [← hord]
      exact ZMod.orderOf_dvd_card_sub_one (CFSG.Timmesfeld.Bang.two_ne_zero_zmod hp2)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have := Nat.le_of_dvd (by omega : 0 < p - 1) hdvd
    omega
  have hm : 12 * f + 1 ≤ m := le_trans hpge hpm
  have hmlower : Nat.factorial (12 * f + 1) / 2 ≤ Nat.factorial m / 2 :=
    Nat.div_le_div_right (Nat.factorial_le hm)
  have hlt : ordTwistedF4 (2 ^ f) < Nat.factorial m / 2 :=
    lt_of_le_of_lt (ordTwistedF4_le_two_pow hf)
      (lt_of_lt_of_le (two_pow_thirty_mul_lt_factorial_div f hf) hmlower)
  rw [h] at hlt
  exact (lt_irrefl _) hlt

private theorem ordTrialityD4_ne_card_alternating {f m : ℕ} (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ f) ≠ Nat.card (alternatingGroup (Fin m)) := by
  intro h
  have hm2 : 2 ≤ m := two_le_of_eq_alt_card (one_lt_ordTrialityD4_of_6048 hf) h
  haveI : Nontrivial (Fin m) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro hcon
      exact Nat.zero_ne_one (congrArg Fin.val hcon)⟩
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  obtain ⟨p, hprim⟩ :=
    exists_isPrimitivePrimeDivisor (k := 12 * f) (by omega) (by omega)
  have hp : p.Prime := hprim.prime
  have hpord : p ∣ ordTrialityD4 (2 ^ f) := by
    have hprof := Timmesfeld.Orders.profile_ordTrialityD4 hf
    have hnot4 : ¬ 12 * f ∣ f * 4 := by
      intro hdvd
      have h31 : 3 ∣ 1 := by
        have h' : f * 12 ∣ f * 4 := by simpa [mul_comm] using hdvd
        have h3 : 12 ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f) h'
        norm_num at h3
      norm_num at h31
    exact (hprof.prim p (12 * f) hprim (by omega)).2
      (Or.inl ⟨by simpa [show f * 12 = 12 * f by ring] using dvd_rfl, hnot4⟩)
  have hp2 : p ≠ 2 := hprim.ne_two (by omega)
  have hpdvd : p ∣ Nat.factorial m := by
    have hpdiv : p ∣ Nat.factorial m / 2 := h ▸ hpord
    have hmul : 2 * (Nat.factorial m / 2) = Nat.factorial m :=
      Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hm2)
    rw [← hmul]
    exact dvd_mul_of_dvd_right hpdiv 2
  have hpm : p ≤ m := (Nat.Prime.dvd_factorial hp).1 hpdvd
  have hpge : 12 * f + 1 ≤ p := by
    have hord : orderOf (2 : ZMod p) = 12 * f :=
      CFSG.Quasithin.orderOf_two_eq_of_isPrimitivePrimeDivisor hprim (by omega)
    haveI : Fact p.Prime := ⟨hp⟩
    have hdvd : 12 * f ∣ p - 1 := by
      rw [← hord]
      exact ZMod.orderOf_dvd_card_sub_one (CFSG.Timmesfeld.Bang.two_ne_zero_zmod hp2)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have := Nat.le_of_dvd (by omega : 0 < p - 1) hdvd
    omega
  have hm : 12 * f + 1 ≤ m := le_trans hpge hpm
  have hmlower : Nat.factorial (12 * f + 1) / 2 ≤ Nat.factorial m / 2 :=
    Nat.div_le_div_right (Nat.factorial_le hm)
  have hlt : ordTrialityD4 (2 ^ f) < Nat.factorial m / 2 :=
    lt_of_le_of_lt (ordTrialityD4_le_two_pow hf)
      (lt_of_lt_of_le (two_pow_thirty_mul_lt_factorial_div f hf) hmlower)
  rw [h] at hlt
  exact (lt_irrefl _) hlt

private theorem ordTits_ne_card_alternating {m : ℕ} :
    ordTits ≠ Nat.card (alternatingGroup (Fin m)) := by
  intro h
  have hm2 : 2 ≤ m := two_le_of_eq_alt_card (by norm_num [F4Pilot.evenLieOrder, ordTits]) h
  haveI : Nontrivial (Fin m) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro hcon
      exact Nat.zero_ne_one (congrArg Fin.val hcon)⟩
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  have hm17 : m ≤ 16 := by
    by_contra hm
    have h17 : 17 ≤ m := by omega
    have hdvd : 17 ∣ Nat.factorial m := (Nat.Prime.dvd_factorial (by norm_num)).2 h17
    have hm2 : 2 ≤ m := by omega
    have hmul : 2 * (Nat.factorial m / 2) = Nat.factorial m :=
      Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hm2)
    have hcop : Nat.Coprime 17 2 := by norm_num
    have hdvd2 : 17 ∣ Nat.factorial m / 2 := by
      apply hcop.dvd_of_dvd_mul_left
      rwa [hmul]
    have h17ord : 17 ∣ ordTits := h ▸ hdvd2
    norm_num [ordTits] at h17ord
  interval_cases m <;> norm_num [ordTits, Nat.factorial] at h

private theorem ordTits_ne_ordG2 {g : ℕ} (hg : 1 ≤ g) : ordTits ≠ ordG2 (2 ^ g) := by
  intro h
  obtain ⟨r, hr, hg'⟩ := (Timmesfeld.Orders.profile_ordG2 hg).two
  have ht : ordTits = 2 ^ 11 * 8775 := Timmesfeld.Orders.ordTits_eq
  have hodd : Odd 8775 := by norm_num
  have heq : 2 ^ 11 * 8775 = 2 ^ (g * 6) * r := by
    rw [← ht]
    exact h.trans hg'
  have := Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd hr heq
  omega

private theorem false_of_classicalEvenAlt {X : Type} [Group X] {t₀ : StatedLieTag} {n : ℕ}
    (hsimple : IsSimpleGroup X)
    (hadm : StatedLieAdmissible t₀ 0 2 n)
    (hcard : Nat.card X = F4Pilot.evenLieOrder t₀ 0 n)
    (hne : t₀ ≠ .PSL ∧ t₀ ≠ .PSU ∧ t₀ ≠ .PSp ∧ t₀ ≠ .POmegaPlus ∧ t₀ ≠ .POmegaMinus)
    (hnePSL2 : ∀ f : ℕ, 1 ≤ f → F4Pilot.evenLieOrder t₀ 0 n ≠ ordA 1 (2 ^ f))
    (hnePSU3 : ∀ f : ℕ, 1 ≤ f → F4Pilot.evenLieOrder t₀ 0 n ≠ ordTwistedA 2 (2 ^ f))
    (h : IsQuasisimple X ∧ ∃ (t : StatedLieTag) (m f : ℕ),
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      LieModel (X ⧸ Subgroup.center X) t m 2 f) : False := by
  obtain ⟨hq, t, m, f, ht, hLie⟩ := h
  have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
  haveI : IsSimpleGroup X := hsimple
  obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hqo
  have hLieX : LieModel X t m 2 f := Blueprint.LieModel.of_mulEquiv e.symm hLie
  have hsc : StatedClassicalModel X t m 2 f :=
    hLieX.statedClassicalModel (by
      rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [classicalTags])
  have hord := CFSG.Timmesfeld.card_statedClassicalModel_two hsc
  have hf : 1 ≤ f := hsc.1.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · have hX : Nat.card X = ordA (m - 1) (2 ^ f) := hord.1 rfl
    have heq : F4Pilot.evenLieOrder t₀ 0 n = ordA (m - 1) (2 ^ f) := hcard.symm.trans hX
    have hm2' : 2 ≤ m := hsc.1.2.2.1
    rcases (by omega : m = 2 ∨ 3 ≤ m) with hm2 | hm3
    · subst hm2
      exact hnePSL2 f hf (by simpa using heq)
    · exact hne.1 (LinearPilot.evenLieOrder_eq_ordA (t := t₀) (n := 0) (g := n)
        (r := m - 1) hadm (by omega) hf heq).1
  · have hX : Nat.card X = ordTwistedA (m - 1) (2 ^ f) := hord.2.1 rfl
    have heq : F4Pilot.evenLieOrder t₀ 0 n = ordTwistedA (m - 1) (2 ^ f) := hcard.symm.trans hX
    have hm3' : 3 ≤ m := hsc.1.2.2.1
    rcases (by omega : m = 3 ∨ 4 ≤ m) with hm3 | hm4
    · subst hm3
      exact hnePSU3 f hf (by simpa using heq)
    · exact hne.2.1 (UnitaryPilot.evenLieOrder_eq_ordTwistedA (t := t₀) (n := 0) (g := n)
        (m := m) hadm (by omega) hf heq).1
  · have hX : Nat.card X = ordBC m (2 ^ f) := hord.2.2.1 rfl
    have heq : F4Pilot.evenLieOrder t₀ 0 n = ordBC m (2 ^ f) := hcard.symm.trans hX
    have hm2' : 2 ≤ m := hsc.1.2.2.1
    exact hne.2.2.1 (SymplecticPilot.evenLieOrder_eq_ordBC (t := t₀) (n := 0) (g := n)
      (m := m) hadm (by omega) hf heq).1
  · have hX : Nat.card X = ordD m (2 ^ f) := hord.2.2.2.1 rfl
    have heq : F4Pilot.evenLieOrder t₀ 0 n = ordD m (2 ^ f) := hcard.symm.trans hX
    have hm4' : 4 ≤ m := hsc.1.2.2
    exact hne.2.2.2.1 (OmegaPilot.evenLieOrder_eq_ordD (t := t₀) (n := 0) (g := n)
      (m := m) hadm (by omega) hf heq).1
  · have hX : Nat.card X = ordTwistedD m (2 ^ f) := hord.2.2.2.2 rfl
    have heq : F4Pilot.evenLieOrder t₀ 0 n = ordTwistedD m (2 ^ f) := hcard.symm.trans hX
    have hm4' : 4 ≤ m := hsc.1.2.2
    exact hne.2.2.2.2 (OmegaPilot.evenLieOrder_eq_ordTwistedD (t := t₀) (n := 0) (g := n)
      (m := m) hadm (by omega) hf heq).1

private theorem false_of_psu33_order {X : Type} [Group X] {M : ℕ} (hcard : Nat.card X = M)
    (hLie : LieModel X .PSU 3 3 1) (hlt : 6048 < M) : False := by
  have h6048 : Nat.card X = 6048 := Blueprint.LieModel.card_psu_three_three hLie
  have : M = 6048 := hcard.symm.trans h6048
  omega

private theorem false_of_isG2 {X : Type} [Group X] {M : ℕ} (hcard : Nat.card X = M)
    {g : ℕ} (hG2 : IsG2 X g) (hne : M ≠ ordG2 (2 ^ g)) : False := by
  have hCE : ChevalleyExceptionalModel X .G2 2 g :=
    Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  have hcardG2 : Nat.card X = ordG2 (2 ^ g) := by
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
  exact hne (hcard.symm.trans hcardG2)

theorem not_classicalEvenAltG2Der_of_is2F4 {X : Type} [Group X] {n : ℕ}
    (h : Is2F4 n X) : ¬ ClassicalEvenAltG2Der X := by
  intro hc
  have hsimple : IsSimpleGroup X :=
    (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n h).2
  have hcard : Nat.card X = F4Pilot.evenLieOrder .twistedF4 0 n := by
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h]
    rfl
  have hadm : StatedLieAdmissible .twistedF4 0 2 n := h.1
  have hn3 : 3 ≤ n := hadm.2.2.2.2.2
  have hn1 : 1 ≤ n := by omega
  have hodd : Odd n := hadm.2.2.2.2.1
  have hneG2 : ∀ g : ℕ, 1 ≤ g → ordTwistedF4 (2 ^ n) ≠ ordG2 (2 ^ g) :=
    fun g hg => CFSG.Quasithin.Vol2.Ch11.SecB.ordTwistedF4_ne_ordG2 hodd hg
  unfold ClassicalEvenAltG2Der at hc
  rcases hc with hcl | hG2Der
  · unfold F12.ClassicalEvenAltG2 at hcl
    rcases hcl with hclassical | hAlt | hG2
    · refine false_of_classicalEvenAlt hsimple hadm hcard (by decide) ?_ ?_ hclassical
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.Quasithin.Vol2.Ch11.SecB.ordTwistedF4_ne_ordA (f := n) (m := 1) (n := f)
            hn1 (by norm_num) hf)
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.Timmesfeld.Orders.ordTwistedF4_ne_ordTwistedA (f := n) (u := 2) (g := f)
            hn1 (by norm_num) hf)
    · obtain ⟨hq, a, hAlt⟩ := hAlt
      have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      haveI : IsSimpleGroup X := hsimple
      obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hqo
      obtain ⟨f⟩ := hAlt
      have hcardAlt : Nat.card X = Nat.card (alternatingGroup (Fin a)) :=
        Nat.card_congr (e.trans f).toEquiv
      exact ordTwistedF4_ne_card_alternating hn1 (hcard.symm.trans hcardAlt)
    · obtain ⟨g, hG2⟩ := hG2
      have hg1 : 1 ≤ g := (Blueprint.LieModel.admissible hG2).2.1
      exact false_of_isG2 hcard hG2 (hneG2 g hg1)
  · obtain ⟨m, hG2Der⟩ := hG2Der
    have hG2Der' : (m = 1 ∧ LieModel X .PSU 3 3 1) ∨ (2 ≤ m ∧ IsG2 X m) := hG2Der
    rcases hG2Der' with ⟨-, hLie⟩ | ⟨hm2, hG2⟩
    · exact false_of_psu33_order hcard hLie (lt_ordTwistedF4_of_three_le hn3)
    · have hm1 : 1 ≤ m := by omega
      exact false_of_isG2 hcard hG2 (hneG2 m hm1)

theorem not_classicalEvenAltG2Der_of_isTits {X : Type} [Group X]
    (h : IsTits X) : ¬ ClassicalEvenAltG2Der X := by
  intro hc
  have hsimple : IsSimpleGroup X :=
    (CFSG.LieType.Simplicity.fam_tits_simplicity X 2 1 h).2
  have hcard : Nat.card X = F4Pilot.evenLieOrder .Tits 0 1 := by
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h]
    rfl
  have hadm : StatedLieAdmissible .Tits 0 2 1 := h.1
  have hneG2 : ∀ g : ℕ, 1 ≤ g → ordTits ≠ ordG2 (2 ^ g) :=
    fun g hg => ordTits_ne_ordG2 hg
  unfold ClassicalEvenAltG2Der at hc
  rcases hc with hcl | hG2Der
  · unfold F12.ClassicalEvenAltG2 at hcl
    rcases hcl with hclassical | hAlt | hG2
    · refine false_of_classicalEvenAlt hsimple hadm hcard (by decide) ?_ ?_ hclassical
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.RankThree.PartOne.S12K.ordTits_ne_ordA_one (g := f) hf)
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.Timmesfeld.Orders.ordTits_ne_ordTwistedA (u := 2) (g := f) (by norm_num) hf)
    · obtain ⟨hq, a, hAlt⟩ := hAlt
      have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      haveI : IsSimpleGroup X := hsimple
      obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hqo
      obtain ⟨f⟩ := hAlt
      have hcardAlt : Nat.card X = Nat.card (alternatingGroup (Fin a)) :=
        Nat.card_congr (e.trans f).toEquiv
      exact ordTits_ne_card_alternating (hcard.symm.trans hcardAlt)
    · obtain ⟨g, hG2⟩ := hG2
      have hg1 : 1 ≤ g := (Blueprint.LieModel.admissible hG2).2.1
      exact false_of_isG2 hcard hG2 (hneG2 g hg1)
  · obtain ⟨m, hG2Der⟩ := hG2Der
    have hG2Der' : (m = 1 ∧ LieModel X .PSU 3 3 1) ∨ (2 ≤ m ∧ IsG2 X m) := hG2Der
    rcases hG2Der' with ⟨-, hLie⟩ | ⟨hm2, hG2⟩
    · exact false_of_psu33_order hcard hLie (by norm_num [F4Pilot.evenLieOrder, ordTits])
    · have hm1 : 1 ≤ m := by omega
      exact false_of_isG2 hcard hG2 (hneG2 m hm1)

theorem not_classicalEvenAltG2Der_of_is3D4 {X : Type} [Group X] {n : ℕ}
    (h : Is3D4 X n) : ¬ ClassicalEvenAltG2Der X := by
  intro hc
  have hCE : ChevalleyExceptionalModel X .trialityD4 2 n :=
    Blueprint.LieModel.chevalleyExceptionalModel h (by decide)
  have hsimple : IsSimpleGroup X :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 n hCE).2
  have hcard : Nat.card X = F4Pilot.evenLieOrder .trialityD4 0 n := by
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE]
    rfl
  have hadm : StatedLieAdmissible .trialityD4 0 2 n := (Blueprint.LieModel.admissible h)
  have hn1 : 1 ≤ n := hadm.2.1
  have hneG2 : ∀ g : ℕ, 1 ≤ g → ordTrialityD4 (2 ^ n) ≠ ordG2 (2 ^ g) :=
    fun g hg => (CFSG.Quasithin.MS93.ordG2_ne_ordTrialityD4 hg hn1).symm
  unfold ClassicalEvenAltG2Der at hc
  rcases hc with hcl | hG2Der
  · unfold F12.ClassicalEvenAltG2 at hcl
    rcases hcl with hclassical | hAlt | hG2
    · refine false_of_classicalEvenAlt hsimple hadm hcard (by decide) ?_ ?_ hclassical
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.RankThree.PartOne.S12K.ordTrialityD4_ne_ordA_one (f := n) (g := f) hn1 hf)
      · intro f hf
        simpa [F4Pilot.evenLieOrder] using
          (CFSG.Timmesfeld.Orders.ordTrialityD4_ne_ordTwistedA (f := n) (u := 2) (g := f)
            hn1 (by norm_num) hf)
    · obtain ⟨hq, a, hAlt⟩ := hAlt
      have hqo : CFSG.Open.IsQuasisimple X := ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      haveI : IsSimpleGroup X := hsimple
      obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hqo
      obtain ⟨f⟩ := hAlt
      have hcardAlt : Nat.card X = Nat.card (alternatingGroup (Fin a)) :=
        Nat.card_congr (e.trans f).toEquiv
      exact ordTrialityD4_ne_card_alternating hn1 (hcard.symm.trans hcardAlt)
    · obtain ⟨g, hG2⟩ := hG2
      have hg1 : 1 ≤ g := (Blueprint.LieModel.admissible hG2).2.1
      exact false_of_isG2 hcard hG2 (hneG2 g hg1)
  · obtain ⟨m, hG2Der⟩ := hG2Der
    have hG2Der' : (m = 1 ∧ LieModel X .PSU 3 3 1) ∨ (2 ≤ m ∧ IsG2 X m) := hG2Der
    rcases hG2Der' with ⟨-, hLie⟩ | ⟨hm2, hG2⟩
    · exact false_of_psu33_order hcard hLie (lt_ordTrialityD4_of_6048 hn1)
    · have hm1 : 1 ≤ m := by omega
      exact false_of_isG2 hcard hG2 (hneG2 m hm1)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
