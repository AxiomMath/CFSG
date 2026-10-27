module

public import CFSG.Quasithin.EmptyFaithful.R3c7Cls
public import CFSG.Quasithin.EmptyFaithful.S152SType

public section

namespace CFSG.Quasithin.S152S

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Ch1 (IsFermatOrMersennePrime IsLemma115SporadicName)

inductive LieShape : ℕ → Prop
  | big2 {N a b : ℕ} (ha : padicValNat 2 N = a) (hb : N < 2 ^ b) (h1 : 3 * b ≤ 8 * a)
      (h2 : b + 2 ≤ 3 * a) : LieShape N
  | l3two {N : ℕ} (h : N = 168) : LieShape N
  | l2two {f N : ℕ} (hf : 2 ≤ f) (h : N = 2 ^ f * ((2 ^ f) ^ 2 - 1)) : LieShape N
  | a6 {N : ℕ} (h : N = 360) : LieShape N

theorem LieShape.of_two_part {N g r a b : ℕ} (hg : Odd g) (hr : Odd r) (h : N * g = 2 ^ a * r)
    (hb : 2 ^ a * r < 2 ^ b) (h1 : 3 * b ≤ 8 * a) (h2 : b + 2 ≤ 3 * a) : LieShape N :=
  LieShape.big2 (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd hg hr h)
    (lt_of_le_of_lt (calc N ≤ N * g := Nat.le_mul_of_pos_right N hg.pos
      _ = 2 ^ a * r := h) hb) h1 h2

section Members

variable {X : Type} [Group X]

theorem lieShape_psl3_two {f : ℕ} (hf : 1 ≤ f) (h : IsPSL 3 2 f X) : LieShape (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := CFSG.Quasithin.R3c6.psl3Data h
  by_cases hf1 : f = 1
  · subst hf1
    refine LieShape.l3two ?_
    norm_num at hN
    exact hN
  · have hf2 : 2 ≤ f := by omega
    have hg : Odd (Nat.gcd 3 (2 ^ f - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have h2 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 2) (by norm_num)
    have h3 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 3) (by norm_num)
    refine LieShape.of_two_part hg (h2.mul h3) (a := f * 3) (b := f * 8) ?_ ?_ (by omega)
      (by omega)
    · rw [hN, pow_mul]
    · have e2 : (2 ^ f) ^ 2 - 1 < (2 ^ f) ^ 2 := Nat.sub_lt (by positivity) one_pos
      have e3 : (2 ^ f) ^ 3 - 1 < (2 ^ f) ^ 3 := Nat.sub_lt (by positivity) one_pos
      calc 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))
          < 2 ^ (f * 3) * ((2 ^ f) ^ 2 * (2 ^ f) ^ 3) :=
            Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' e2 e3) (by positivity)
        _ = 2 ^ (f * 8) := by ring

theorem lieShape_psu3_two {f : ℕ} (hf : 2 ≤ f) (h : IsPSU 3 2 f X) : LieShape (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := CFSG.Quasithin.R3c6.psu3Data h
  have hf1 : 1 ≤ f := by omega
  have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have h2 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf1 (a := 2) (by norm_num)
  have h3 := CFSG.Timmesfeld.Orders.odd_pow_add_one hf1 (a := 3) (by norm_num)
  refine LieShape.of_two_part hg (h2.mul h3) (a := f * 3) (b := f * 8) ?_ ?_ (by omega)
    (by omega)
  · rw [hN, pow_mul]
  · have hQ : 2 ≤ 2 ^ f :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    have e : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) < (2 ^ f) ^ 2 * (2 ^ f) ^ 3 := by
      have h23 : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [h1]
      nlinarith
    calc 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))
        < 2 ^ (f * 3) * ((2 ^ f) ^ 2 * (2 ^ f) ^ 3) :=
          Nat.mul_lt_mul_of_pos_left e (by positivity)
      _ = 2 ^ (f * 8) := by ring

theorem lieShape_psp4_two {f : ℕ} (hf : 1 ≤ f) (h : StatedClassicalModel X .PSp 2 2 f) :
    LieShape (Nat.card X) := by
  have hN : Nat.card X = CFSG.Open.ordBC 2 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  rw [CFSG.Quasithin.R3c6.ordBC_two_eq hf] at hN
  have h2 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 2) (by norm_num)
  have h4 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 4) (by norm_num)
  have hQ : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  refine LieShape.of_two_part (g := 1) odd_one (h2.mul h4) (a := f * 4) (b := f * 10)
    (by rw [mul_one, hN]) ?_ (by omega) (by omega)
  have := CFSG.Quasithin.R3c6.two_pow_mul_lt (f := f) (a := 4) (k := 6)
    (r := ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) (by
    calc ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) < (2 ^ f) ^ 2 * (2 ^ f) ^ 4 :=
          Nat.mul_lt_mul'' (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ)
            (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ)
      _ = (2 ^ f) ^ 6 := by ring)
  simpa using this

theorem lieShape_psl2_two {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 2 2 f X) : LieShape (Nat.card X) := by
  obtain ⟨-, -, -, hN⟩ := CFSG.Quasithin.R3c6.psl2Data h
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega : 0 < f)))
  rw [hg, mul_one] at hN
  exact LieShape.l2two hf hN

theorem lieShape_u33 (h : IsPSU 3 3 1 X) : LieShape (Nat.card X) := by
  obtain ⟨-, -, -, -, hN⟩ := CFSG.Quasithin.R3c6.psu3Data h
  have hN' : Nat.card X = 6048 := by simpa using hN
  exact LieShape.of_two_part (g := 1) odd_one (by decide : Odd 189) (a := 5) (b := 13)
    (by rw [hN']; norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lieShape_l4 (h : StatedClassicalModel X .PSL 4 2 1) : LieShape (Nat.card X) := by
  have hN : Nat.card X = CFSG.Open.ordA (4 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have h20160 : CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 := by decide
  exact LieShape.of_two_part (g := 1) odd_one (by decide : Odd 315) (a := 6) (b := 15)
    (by rw [hN, h20160]; norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lieShape_l5 (h : StatedClassicalModel X .PSL 5 2 1) : LieShape (Nat.card X) := by
  have hN : Nat.card X = CFSG.Open.ordA (5 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have h9999360 : CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 := by decide
  exact LieShape.of_two_part (g := 1) odd_one (by decide : Odd 9765) (a := 10) (b := 24)
    (by rw [hN, h9999360]; norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lieShape_alt6 (e : X ≃* alternatingGroup (Fin 6)) : LieShape (Nat.card X) := by
  have hN : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact LieShape.a6 hN

end Members

section Exc

open CFSG.Open (ordG2 ordTrialityD4 ordTwistedF4 ordTits ordSuzuki)

variable {X : Type} [Group X]

theorem lieShape_g2_two {f : ℕ} (hf : 1 ≤ f) (h : ChevalleyExceptionalModel X .G2 2 f) :
    LieShape (Nat.card X) := by
  have hN : Nat.card X = ordG2 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  rw [CFSG.Timmesfeld.Orders.ordG2_eq] at hN
  have h6 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 6) (by norm_num)
  have h2 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 2) (by norm_num)
  have hQ : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  refine LieShape.of_two_part (g := 1) odd_one (h6.mul h2) (a := f * 6) (b := f * 14)
    (by rw [mul_one, hN]) ?_ (by omega) (by omega)
  have := CFSG.Quasithin.R3c6.two_pow_mul_lt (f := f) (a := 6) (k := 8)
    (r := ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) (by
    calc ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 6 * (2 ^ f) ^ 2 :=
          Nat.mul_lt_mul'' (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ)
            (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ)
      _ = (2 ^ f) ^ 8 := by ring)
  simpa using this

theorem lieShape_3d4_two {f : ℕ} (hf : 1 ≤ f) (h : ChevalleyExceptionalModel X .trialityD4 2 f) :
    LieShape (Nat.card X) := by
  have hN : Nat.card X = ordTrialityD4 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  have hm : ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    rw [ordTrialityD4, pow_mul]; ring
  rw [hm] at hN
  have hE : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have h1 : Odd ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) :=
    (((Nat.even_pow' (by norm_num)).2 hE).add ((Nat.even_pow' (by norm_num)).2 hE)).add_one
  have h6 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 6) (by norm_num)
  have h2 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 2) (by norm_num)
  have hQ2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ : 1 ≤ 2 ^ f := by omega
  refine LieShape.of_two_part (g := 1) odd_one (h1.mul (h6.mul h2)) (a := f * 12) (b := f * 29)
    (by rw [mul_one, hN]) ?_ (by omega) (by omega)
  have hlt : (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 < (2 ^ f) ^ 9 := by
    set Q := 2 ^ f with hQdef
    have hQ4 : 16 ≤ Q ^ 4 :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ2 4
    have h8 : Q ^ 8 = Q ^ 4 * Q ^ 4 := by ring
    have h9 : Q ^ 9 = Q * Q ^ 8 := by ring
    nlinarith
  have := CFSG.Quasithin.R3c6.two_pow_mul_lt (f := f) (a := 12) (k := 17)
    (r := ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) (by
    calc ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))
        < (2 ^ f) ^ 9 * ((2 ^ f) ^ 6 * (2 ^ f) ^ 2) :=
          Nat.mul_lt_mul'' hlt (Nat.mul_lt_mul'' (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ)
            (CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ))
      _ = (2 ^ f) ^ 17 := by ring)
  simpa using this

theorem lieShape_2f4_two {f : ℕ} (hf : 1 ≤ f) (h : ReeTitsModel X .twistedF4 2 f) :
    LieShape (Nat.card X) := by
  have hN : Nat.card X = ordTwistedF4 (2 ^ f) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
  have hm : ordTwistedF4 (2 ^ f) = 2 ^ (f * 12) * (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    rw [ordTwistedF4, pow_mul]; ring
  rw [hm] at hN
  have h6 := CFSG.Timmesfeld.Orders.odd_pow_add_one hf (a := 6) (by norm_num)
  have h4 := CFSG.Timmesfeld.Orders.odd_pow_sub_one hf (a := 4) (by norm_num)
  have h3 := CFSG.Timmesfeld.Orders.odd_pow_add_one hf (a := 3) (by norm_num)
  have h1 := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega : 0 < f)
  have hQ2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ : 1 ≤ 2 ^ f := by omega
  refine LieShape.of_two_part (g := 1) odd_one (h6.mul (h4.mul (h3.mul h1))) (a := f * 12)
    (b := f * 28) (by rw [mul_one, hN]) ?_ (by omega) (by omega)
  have e1 : (2 ^ f) ^ 6 + 1 < (2 ^ f) ^ 7 :=
    CFSG.Quasithin.R3c6.pow_add_one_lt _ 6 hQ2 (by norm_num)
  have e3 : (2 ^ f) ^ 3 + 1 < (2 ^ f) ^ 4 :=
    CFSG.Quasithin.R3c6.pow_add_one_lt _ 3 hQ2 (by norm_num)
  have e4 : (2 ^ f) ^ 4 - 1 < (2 ^ f) ^ 4 := CFSG.Quasithin.R3c6.sub_one_lt_pow _ _ hQ
  have e0 : 2 ^ f - 1 < 2 ^ f := Nat.sub_lt hQ one_pos
  have := CFSG.Quasithin.R3c6.two_pow_mul_lt (f := f) (a := 12) (k := 16)
    (r := ((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) * (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) (by
    calc ((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) * (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))
        < (2 ^ f) ^ 7 * ((2 ^ f) ^ 4 * ((2 ^ f) ^ 4 * 2 ^ f)) :=
          Nat.mul_lt_mul'' e1 (Nat.mul_lt_mul'' e4 (Nat.mul_lt_mul'' e3 e0))
      _ = (2 ^ f) ^ 16 := by ring)
  simpa using this

end Exc

section Sz

variable {X : Type} [Group X]

theorem lieShape_sz {f : ℕ} (hf : 2 ≤ f) (h : SuzukiModel X 2 f) : LieShape (Nat.card X) := by
  obtain ⟨-, a, -, -, hN⟩ := CFSG.GH74.card_of_suzukiModel h
  have hsz : CFSG.Open.ordSuzuki (2 ^ f) = 2 ^ (f * 2) * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    rw [CFSG.Open.ordSuzuki, pow_mul, mul_assoc]
  rw [hsz] at hN
  have hf1 : 1 ≤ f := by omega
  have h2 := CFSG.Timmesfeld.Orders.odd_pow_add_one hf1 (a := 2) (by norm_num)
  have h1 := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega : 0 < f)
  have hQ2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hQ : 1 ≤ 2 ^ f := by omega
  refine LieShape.of_two_part (g := 1) odd_one (h2.mul h1) (a := f * 2) (b := f * 5)
    (by rw [mul_one, hN]) ?_ (by omega) (by omega)
  have e : ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1) < (2 ^ f) ^ 3 := by
    set Q := 2 ^ f with hQdef
    have hQ' : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
    zify [hQ]
    nlinarith [hQ']
  have := CFSG.Quasithin.R3c6.two_pow_mul_lt (f := f) (a := 2) (k := 3)
    (r := ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) e
  simpa using this

end Sz

section Tits

variable {X : Type} [Group X]


theorem lieShape_tits {f : ℕ} (h : ReeTitsModel X .Tits 2 f) : LieShape (Nat.card X) := by
  have hN : Nat.card X = CFSG.Open.ordTits := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h
  rw [CFSG.Timmesfeld.Orders.ordTits_eq] at hN
  exact LieShape.of_two_part (g := 1) odd_one (by decide : Odd 8775) (a := 11) (b := 25)
    (by rw [mul_one, hN]) (by norm_num) (by norm_num) (by norm_num)

end Tits

section Cat

open CFSG.QuasithinUnique (Lemma115LieCharTwo)

theorem lieShape_lieCharTwo {X : Type} [Group X] (hlie : Lemma115LieCharTwo X) :
    LieShape (Nat.card X) := by
  rcases hlie with ((⟨f, hfam⟩ | hTits) | ⟨n, hn, hPSL⟩) | ⟨⟨e⟩⟩ | hU33
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩
    · exact lieShape_psl2_two hf hm
    · exact lieShape_psl3_two hf hm
    · exact lieShape_psu3_two hf hm
    · exact lieShape_psp4_two (by omega) hm
    · exact lieShape_g2_two (by omega) hm
    · exact lieShape_3d4_two hf hm
    · exact lieShape_2f4_two (by omega) hm
    · exact lieShape_sz (by omega) hm
  · exact lieShape_tits hTits
  · rcases hn with rfl | rfl
    · exact lieShape_l4 hPSL
    · exact lieShape_l5 hPSL
  · exact lieShape_alt6 e
  · exact lieShape_u33 hU33

end Cat

section Numbers

theorem LieShape.false_of_numbers {N a₀ B : ℕ} (hν : padicValNat 2 N = a₀) (hB : 8 * a₀ < 3 * (B + 1))
    (hNB : 2 ^ B ≤ N) (h168 : N ≠ 168) (h360 : N ≠ 360) (hl2 : N ≠ 2 ^ a₀ * ((2 ^ a₀) ^ 2 - 1))
    (h : LieShape N) : False := by
  cases h with
  | big2 ha hb h1 h2 =>
    rename_i a b
    have hab : a = a₀ := ha.symm.trans hν
    subst hab
    have hbB : b ≤ B := by omega
    have : N < 2 ^ B := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hbB)
    omega
  | l3two h => exact h168 h
  | l2two hf h =>
    rename_i f
    have hodd : Odd ((2 ^ f) ^ 2 - 1) :=
      CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (a := 2) (by norm_num)
    have hf' : padicValNat 2 N = f :=
      CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) odd_one hodd (by rw [mul_one]; exact h)
    have hfa : f = a₀ := hf'.symm.trans hν
    subst hfa
    exact hl2 h
  | a6 h => exact h360 h

theorem not_lieShape_alt7 : ¬ LieShape 2520 :=
  fun h => LieShape.false_of_numbers (a₀ := 3) (B := 8)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 315) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_M11 : ¬ LieShape 7920 :=
  fun h => LieShape.false_of_numbers (a₀ := 4) (B := 10)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 495) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_M12 : ¬ LieShape 95040 :=
  fun h => LieShape.false_of_numbers (a₀ := 6) (B := 16)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 1485) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_M22 : ¬ LieShape 443520 :=
  fun h => LieShape.false_of_numbers (a₀ := 7) (B := 18)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 3465) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_M23 : ¬ LieShape 10200960 :=
  fun h => LieShape.false_of_numbers (a₀ := 7) (B := 18)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 79695) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_M24 : ¬ LieShape 244823040 :=
  fun h => LieShape.false_of_numbers (a₀ := 10) (B := 26)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 239085) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_J2 : ¬ LieShape 604800 :=
  fun h => LieShape.false_of_numbers (a₀ := 7) (B := 18)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 4725) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_J4 : ¬ LieShape 86775571046077562880 :=
  fun h => LieShape.false_of_numbers (a₀ := 21) (B := 56)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 41377816699065) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_HS : ¬ LieShape 44352000 :=
  fun h => LieShape.false_of_numbers (a₀ := 9) (B := 24)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 86625) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_He : ¬ LieShape 4030387200 :=
  fun h => LieShape.false_of_numbers (a₀ := 10) (B := 26)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 3935925) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem not_lieShape_Ru : ¬ LieShape 145926144000 :=
  fun h => LieShape.false_of_numbers (a₀ := 14) (B := 37)
    (CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) (r := 8906625) odd_one (by decide)
      (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

end Numbers

section Exclusions


theorem notLieCharTwoAlt7 : NotLieCharTwoAlt7 := by
  intro X _ _ ⟨e⟩ hlie
  have hN : Nat.card X = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h := lieShape_lieCharTwo hlie
  rw [hN] at h
  exact not_lieShape_alt7 h

end Exclusions

section Spor


theorem notLieCharTwoSporadic : NotLieCharTwoSporadic := by
  intro K _ _ hq s hs ⟨he⟩ hlie
  have hp : Group.IsPerfect K := hq.1
  have hsimp : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (CFSG.Quasithin.R3c7.isSimpleGroup_sporadic hs) he
  have hperf : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := by
    have := hp
    infer_instance
  have hcen := CFSG.Quasithin.R3c3.center_eq_bot_of_simple_perfect hsimp hperf
  have hZ : Subgroup.center K = CFSG.pCore 2 K := by
    refine le_antisymm (fun x hx => ?_)
      (CFSG.QuasithinUnique.Id2519.pCore_le_center_of_isQuasisimple hq)
    have hmem : (QuotientGroup.mk x : K ⧸ CFSG.pCore 2 K) ∈
        Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]
    rw [hcen, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).1 hmem
  have hcard : Nat.card (K ⧸ Subgroup.center K) = Nat.card (NativeSporadic.Carrier s) := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
    exact Nat.card_congr he.toEquiv
  have h := lieShape_lieCharTwo hlie
  rw [hcard] at h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
    rw [hc] at h
    exact not_lieShape_M11 h
  · have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
    rw [hc] at h
    exact not_lieShape_M12 h
  · have hc : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [hc] at h
    exact not_lieShape_M22 h
  · have hc : Nat.card (NativeSporadic.Carrier .M23) = 10200960 := CFSG.Quasithin.R3c6.card_M23
    rw [hc] at h
    exact not_lieShape_M23 h
  · have hc : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
    rw [hc] at h
    exact not_lieShape_M24 h
  · have hc : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
    rw [hc] at h
    exact not_lieShape_J2 h
  · have hc : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
      CFSG.Sporadic.J4.card_J4
    rw [hc] at h
    exact not_lieShape_J4 h
  · have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
    rw [hc] at h
    exact not_lieShape_HS h
  · have hc : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
    rw [hc] at h
    exact not_lieShape_He h
  · have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
    rw [hc] at h
    exact not_lieShape_Ru h

end Spor

end CFSG.Quasithin.S152S
