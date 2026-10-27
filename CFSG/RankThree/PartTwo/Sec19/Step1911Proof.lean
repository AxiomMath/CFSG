module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.Classical
import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp projOmegaMinus)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL StatedSp StatedOmega StatedQuadMinus
  StatedClassicalModel)
open CFSG.Open (ordA ordTwistedD ordG2 ordTrialityD4)

namespace Step1911Proof

theorem ordTrialityD4_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTrialityD4 q =
      (q ^ 2 - 1) ^ 2 * (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 4 + q ^ 2 + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  rw [ordTrialityD4]
  zify [h2, h6]
  ring

theorem ordTrialityD4_two_pow (f : ℕ) :
    ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
  rw [ordTrialityD4, pow_mul]
  ring

theorem odd_trialityOddPart {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
  have he : Even ((2 ^ f) ^ 8 + (2 ^ f) ^ 4) := by
    rw [← pow_mul, ← pow_mul]
    exact ((Nat.even_pow' (by omega)).mpr even_two).add ((Nat.even_pow' (by omega)).mpr even_two)
  exact he.add_one.mul ((Timmesfeld.Orders.odd_pow_sub_one hf (by norm_num)).mul
    (Timmesfeld.Orders.odd_pow_sub_one hf (by norm_num)))

theorem ordTrialityD4_le {a b : ℕ} (hab : a ≤ b) : ordTrialityD4 a ≤ ordTrialityD4 b := by
  unfold ordTrialityD4
  gcongr

theorem ordTrialityD4_values :
    ordTrialityD4 2 = 211341312 ∧ ordTrialityD4 3 = 20560831566912 ∧
      ordTrialityD4 4 = 67802350642790400 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ordTrialityD4]

theorem ne_ordTrialityD4 {N q : ℕ} (hq : 2 ≤ q) (hN : N < 67802350642790400)
    (h2 : N ≠ 211341312) (h3 : N ≠ 20560831566912) : N ≠ ordTrialityD4 q := by
  obtain ⟨e2, e3, e4⟩ := ordTrialityD4_values
  intro h
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · interval_cases q
    · exact h2 (h.trans e2)
    · exact h3 (h.trans e3)
  · have := ordTrialityD4_le h4
    omega

theorem false_of_odd {N m q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hdvd : 2 ^ N ∣ m)
    (hlt : m < 2 ^ (3 * N)) (h : m = ordTrialityD4 q) : False := by
  rw [ordTrialityD4_eq (by omega)] at h
  have hs : Odd (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 4 + q ^ 2 + 1)) :=
    (hq.pow.mul (hq.pow.add_odd hq.pow).add_one).mul (hq.pow.add_odd hq.pow).add_one
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < (q ^ 2 - 1) ^ 2 := pow_pos (by omega) 2
  have hdvd' : 2 ^ N ∣ (q ^ 2 - 1) ^ 2 :=
    (Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr hs)).dvd_of_dvd_mul_right (h ▸ hdvd)
  have hle : 2 ^ N ≤ (q ^ 2 - 1) ^ 2 := Nat.le_of_dvd hpos hdvd'
  have hlt4 : (q ^ 2 - 1) ^ 2 < q ^ 4 := by
    calc (q ^ 2 - 1) ^ 2 < (q ^ 2) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      _ = q ^ 4 := by ring
  have h12 : 2 ^ (3 * N) < q ^ 12 := by
    calc 2 ^ (3 * N) = (2 ^ N) ^ 3 := by rw [← pow_mul, mul_comm]
      _ < (q ^ 4) ^ 3 := Nat.pow_lt_pow_left (hle.trans_lt hlt4) (by norm_num)
      _ = q ^ 12 := by ring
  have hs12 : q ^ 12 ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 4 + q ^ 2 + 1) := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hge : q ^ 12 ≤ m := by
    rw [h]
    exact hs12.trans (Nat.le_mul_of_pos_left _ hpos)
  exact lt_irrefl _ ((h12.trans_le hge).trans hlt)

theorem false_of_two_pow {m g M r : ℕ} (hg : g ∣ 3) (hr : Odd r) (hm : m * g = 2 ^ M * r)
    (hlt : 2 ^ M * r < 2 ^ (3 * M))
    (h2 : ∀ f : ℕ, 1 ≤ f → M = f * 12 →
      ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) * g ≠ r)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : m = ordTrialityD4 (p ^ f)) : False := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have hgodd : Odd g := Odd.of_dvd_nat (by decide) hg
  by_cases hp2 : p = 2
  · subst hp2
    rw [h, ordTrialityD4_two_pow, mul_assoc] at hm
    have hM := Timmesfeld.Orders.eq_of_two_pow_mul_odd ((odd_trialityOddPart hf).mul hgodd) hr hm
    subst hM
    exact h2 f hf rfl (Nat.eq_of_mul_eq_mul_left (by positivity) hm)
  · have hq3 : 3 ≤ p ^ f :=
      (show 3 ≤ p by have := hp.two_le; omega).trans (Nat.le_self_pow (by omega) p)
    have hdvd : 2 ^ M ∣ m :=
      (Nat.Coprime.pow_left M (Nat.coprime_two_left.mpr hgodd)).dvd_of_dvd_mul_right ⟨r, hm⟩
    have hmle : m ≤ 2 ^ M * r := (Nat.le_mul_of_pos_right m hg0).trans_eq hm
    exact false_of_odd (hp.odd_of_ne_two hp2).pow hq3 hdvd (hmle.trans_lt hlt) h

theorem two_pow_mul_lt {n c a b : ℕ} (hab : a + b ≤ 2 * c) :
    2 ^ (n * c) * (((2 ^ n) ^ a - 1) * ((2 ^ n) ^ b - 1)) < 2 ^ (3 * (n * c)) := by
  have h1 : ((2 ^ n) ^ a - 1) * ((2 ^ n) ^ b - 1) < (2 ^ n) ^ a * (2 ^ n) ^ b :=
    Nat.mul_lt_mul_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) (Nat.sub_le _ _)
      (by positivity)
  have h2 : (2 ^ n) ^ a * (2 ^ n) ^ b ≤ 2 ^ (n * c * 2) := by
    rw [← pow_add, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.mul_le_mul_left n hab).trans_eq (by ring))
  calc 2 ^ (n * c) * (((2 ^ n) ^ a - 1) * ((2 ^ n) ^ b - 1))
      < 2 ^ (n * c) * 2 ^ (n * c * 2) :=
        Nat.mul_lt_mul_of_pos_left (h1.trans_le h2) (by positivity)
    _ = 2 ^ (3 * (n * c)) := by rw [← pow_add]; ring_nf

theorem lt_SL3 {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) * 3 < (q ^ 8 - 1) * (q ^ 12 - 1) := by
  have h1 : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  zify [h1 2, h1 6, h1 8, h1 12]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set x : ℤ := (q : ℤ) with hx
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 16 ≤ x ^ 4 := by nlinarith
  have hx6 : 1 ≤ x ^ 6 := by nlinarith
  have hA : 0 < x ^ 8 + x ^ 4 + 1 := by positivity
  have hB : 0 < x ^ 2 - 1 := by linarith
  have hC : 0 < x ^ 10 + x ^ 8 - 3 * x ^ 6 - x ^ 2 + 2 := by
    have e : x ^ 10 + x ^ 8 - 3 * x ^ 6 - x ^ 2 + 2 =
        x ^ 6 * (x ^ 4 - 16) + 13 * x ^ 6 + x ^ 2 * (x ^ 6 - 1) + 2 := by ring
    have h6 : 0 ≤ x ^ 6 * (x ^ 4 - 16) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ x ^ 2 * (x ^ 6 - 1) := mul_nonneg (by positivity) (by linarith)
    rw [e]
    linarith
  have key : (x ^ 8 - 1) * (x ^ 12 - 1) - (x ^ 8 + x ^ 4 + 1) * ((x ^ 6 - 1) * (x ^ 2 - 1)) * 3 =
      (x ^ 8 + x ^ 4 + 1) * (x ^ 2 - 1) * (x ^ 10 + x ^ 8 - 3 * x ^ 6 - x ^ 2 + 2) := by ring
  linarith [mul_pos (mul_pos hA hB) hC]

theorem lt_Sp4 {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) < (q ^ 6 - 1) * (q ^ 12 - 1) := by
  have h1 : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  zify [h1 2, h1 6, h1 12]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set x : ℤ := (q : ℤ) with hx
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx6 : 2 ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) hq' 6
  have hpos : 0 < (x ^ 6 - 1) * (x ^ 8 + x ^ 4 + 1) * x ^ 2 * (x ^ 2 - 1) :=
    mul_pos (mul_pos (mul_pos (by linarith) (by positivity)) (by positivity)) (by linarith)
  have key : (x ^ 6 - 1) * (x ^ 12 - 1) - (x ^ 8 + x ^ 4 + 1) * ((x ^ 6 - 1) * (x ^ 2 - 1)) =
      (x ^ 6 - 1) * (x ^ 8 + x ^ 4 + 1) * x ^ 2 * (x ^ 2 - 1) := by ring
  linarith

theorem lt_G2 {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) < (q ^ 12 - 1) * (q ^ 4 - 1) := by
  have h1 : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  zify [h1 2, h1 4, h1 6, h1 12]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  set x : ℤ := (q : ℤ) with hx
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hpos : 0 < x ^ 2 * (x ^ 2 - 1) ^ 2 * (x ^ 8 + x ^ 4 + 1) :=
    mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) (by positivity)
  have key : (x ^ 12 - 1) * (x ^ 4 - 1) - (x ^ 8 + x ^ 4 + 1) * ((x ^ 6 - 1) * (x ^ 2 - 1)) =
      x ^ 2 * (x ^ 2 - 1) ^ 2 * (x ^ 8 + x ^ 4 + 1) := by ring
  linarith

theorem false_of_SL3 {m g n : ℕ} (hn : 1 ≤ n) (hg : g ∣ 3)
    (hm : m * g = 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : m = ordTrialityD4 (p ^ f)) : False := by
  refine false_of_two_pow hg ((Timmesfeld.Orders.odd_pow_sub_one hn two_pos).mul
    (Timmesfeld.Orders.odd_pow_sub_one hn three_pos)) hm
    (two_pow_mul_lt (by norm_num)) (fun f' hf' hM => ?_) hp hf h
  obtain rfl : n = 4 * f' := by omega
  have e2 : (2 ^ (4 * f')) ^ 2 = (2 ^ f') ^ 8 := by rw [← pow_mul, ← pow_mul]; ring_nf
  have e3 : (2 ^ (4 * f')) ^ 3 = (2 ^ f') ^ 12 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [e2, e3]
  exact ne_of_lt ((Nat.mul_le_mul_left _ (Nat.le_of_dvd (by norm_num) hg)).trans_lt
    (lt_SL3 (Nat.le_self_pow (by omega) 2)))

theorem false_of_Sp4 {m n : ℕ} (hn : 1 ≤ n)
    (hm : m = 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)))
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : m = ordTrialityD4 (p ^ f)) : False := by
  refine false_of_two_pow (one_dvd 3) ((Timmesfeld.Orders.odd_pow_sub_one hn two_pos).mul
    (Timmesfeld.Orders.odd_pow_sub_one hn four_pos)) (by rw [mul_one, hm])
    (two_pow_mul_lt (by norm_num)) (fun f' hf' hM => ?_) hp hf h
  obtain rfl : n = 3 * f' := by omega
  have e2 : (2 ^ (3 * f')) ^ 2 = (2 ^ f') ^ 6 := by rw [← pow_mul, ← pow_mul]; ring_nf
  have e4 : (2 ^ (3 * f')) ^ 4 = (2 ^ f') ^ 12 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [e2, e4, mul_one]
  exact ne_of_lt (lt_Sp4 (Nat.le_self_pow (by omega) 2))

theorem false_of_G2 {m n : ℕ} (hn : 1 ≤ n)
    (hm : m = 2 ^ (n * 6) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)))
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : m = ordTrialityD4 (p ^ f)) : False := by
  refine false_of_two_pow (one_dvd 3)
    ((Timmesfeld.Orders.odd_pow_sub_one (a := 6) hn (by norm_num)).mul
    (Timmesfeld.Orders.odd_pow_sub_one hn two_pos)) (by rw [mul_one, hm])
    (two_pow_mul_lt (by norm_num)) (fun f' hf' hM => ?_) hp hf h
  obtain rfl : n = 2 * f' := by omega
  have e6 : (2 ^ (2 * f')) ^ 6 = (2 ^ f') ^ 12 := by rw [← pow_mul, ← pow_mul]; ring_nf
  have e2 : (2 ^ (2 * f')) ^ 2 = (2 ^ f') ^ 4 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [e6, e2, mul_one]
  exact ne_of_lt (lt_G2 (Nat.le_self_pow (by omega) 2))

theorem card_of_trialityD4
    {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f) :
    p.Prime ∧ 1 ≤ f ∧ Nat.card X = ordTrialityD4 (p ^ f) := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  refine ⟨hp, hf, ?_⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf hm
  · exact ClassicalInvolution.card_of_twistedChevalleyModel_D4_of_ne_two hp hp2 hf hm

theorem card_SL3 {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) =
      2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    GaloisField.card 2 n (by omega), show Finset.Icc 2 3 = {2, 3} by rfl,
    Finset.prod_pair (by norm_num), pow_mul]

theorem card_projSL {m e : ℕ} (hm : 1 ≤ m) (he : 1 ≤ e) :
    Nat.card (projSL m (GaloisField 2 e)) = ordA (m - 1) (2 ^ e) := by
  let φ : StatedProj (StatedSL m (GaloisField 2 e)) ≃* projSL m (GaloisField 2 e) :=
    (Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSL_eq_projSL m _))
  rw [← Nat.card_congr φ.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSL hm,
    GaloisField.card 2 e (by omega), ordA, Nat.sub_add_cancel hm, mul_comm (m - 1) m]

theorem ordA_two_mul_gcd (n : ℕ) :
    ordA 2 (2 ^ n) * Nat.gcd 3 (2 ^ n - 1) =
      2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have hdvd : Nat.gcd 3 (2 ^ n - 1) ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (Nat.gcd_dvd_right _ _).trans (((Nat.sub_one_dvd_pow_sub_one _ 2).mul_right _).mul_left _)
  rw [ordA, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num),
    show 2 * (2 + 1) / 2 = 3 by rfl, show (2 + 1 : ℕ) = 3 by rfl, Nat.div_mul_cancel hdvd,
    pow_mul]

theorem card_projSp (m : ℕ) {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSp m (GaloisField 2 e)) =
      (2 ^ e) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, ((2 ^ e) ^ (2 * j) - 1) := by
  let φ : StatedProj (StatedSp m (GaloisField 2 e)) ≃* projSp m (GaloisField 2 e) :=
    (Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSp_eq_projSp m _))
  rw [← Nat.card_congr φ.toEquiv,
    Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, GaloisField.card 2 e (by omega)]

theorem card_projSp_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSp 2 (GaloisField 2 n)) =
      2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  rw [card_projSp 2 hn, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num),
    pow_mul 2 n 4]
  norm_num

theorem card_isoGTwoEven
    {X : Type} [Group X] {n : ℕ}
    (h : Sec8.IsoGTwoEven X n) : Nat.card X = ordG2 (2 ^ n) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]

theorem card_projSU_four {b : ℕ} (hb : 1 ≤ b) :
    Nat.card (projSU 4 2 b) =
      (2 ^ b) ^ 6 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1)) := by
  rw [Sec21.card_projSU le_rfl hb, show (4 - 1 : ℕ) = 3 by rfl, Sec21.ordTwistedA_three_eq hb]

theorem card_projOmegaMinus {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (projOmegaMinus 3 (GaloisField 2 1) b c) = ordTwistedD 4 (2 ^ 1) := by
  have hm : StatedClassicalModel (projOmegaMinus 3 (GaloisField 2 1) b c) .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, b, c, hbc,
      ⟨((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
        (MulEquiv.subgroupCongr
          (PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c))).symm⟩⟩
  exact (Timmesfeld.card_statedClassicalModel_two hm).2.2.2.2 rfl

theorem not_isList194_of_trialityD4
    {X : Type} [Group X]
    (hX : IsList194 X) {p f : ℕ}
    (hD4 : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f) : False := by
  obtain ⟨hp, hf, hcard⟩ := card_of_trialityD4 hD4
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hne : ∀ N : ℕ, N < 67802350642790400 → N ≠ 211341312 → N ≠ 20560831566912 →
      Nat.card X = N → False := fun N hN h2 h3 hXN =>
    ne_ordTrialityD4 hq hN h2 h3 (hXN.symm.trans hcard)
  rcases hX with ⟨n, hn, h | h | h | hG2⟩ | h | h | h | h | h | h | h | h | ⟨b, c, hbc, h⟩ | h
  ·
    obtain ⟨e⟩ := h
    exact false_of_SL3 hn (one_dvd 3)
      (by rw [mul_one, Nat.card_congr e.toEquiv, card_SL3 hn]) hp hf hcard
  ·
    obtain ⟨e⟩ := h
    exact false_of_SL3 hn (Nat.gcd_dvd_left 3 (2 ^ n - 1))
      (by rw [Nat.card_congr e.toEquiv, card_projSL (by norm_num) hn]; exact ordA_two_mul_gcd n)
      hp hf hcard
  ·
    obtain ⟨e⟩ := h
    exact false_of_Sp4 hn (by rw [Nat.card_congr e.toEquiv, card_projSp_two hn]) hp hf hcard
  ·
    exact false_of_G2 hn (by rw [card_isoGTwoEven hG2, Timmesfeld.Orders.ordG2_eq]) hp hf hcard
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSU_four le_rfl)) <;>
      norm_num
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSU_four (by norm_num))) <;>
      norm_num
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSL (by norm_num) le_rfl)) <;>
      decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_
      ((Nat.card_congr e.toEquiv).trans (card_projSL (by norm_num) (by norm_num))) <;> decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSL (by norm_num) le_rfl)) <;>
      decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSL (by norm_num) le_rfl)) <;>
      decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSL (by norm_num) le_rfl)) <;>
      decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projSp 3 le_rfl)) <;> decide
  ·
    obtain ⟨e⟩ := h
    refine hne _ ?_ ?_ ?_ ((Nat.card_congr e.toEquiv).trans (card_projOmegaMinus hbc)) <;> decide
  ·
    obtain ⟨e⟩ := h
    refine hne 1814400 (by norm_num) (by norm_num) (by norm_num) ?_
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem false_of_isExtOf {G : Type} [Group G] {E L K H : Subgroup G} (hE : IsE27 E)
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) (hLK : L ≤ K) (hEH : E ≤ H)
    (hext : Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (starIm K H) = 1920 := by
    obtain ⟨N, hN, hN1, hN2⟩ := hext
    obtain ⟨eN⟩ := hN1
    obtain ⟨eQ⟩ := hN2
    rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eN.toEquiv, Nat.card_perm, Nat.card_fin,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ _), Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    decide
  have hELK : E ⊓ L ≤ K := inf_le_right.trans hLK
  let φ : (E ⊓ L : Subgroup G) →* starIm K H :=
    ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hELK)).codRestrict
      (starIm K H) fun x => ⟨Subgroup.inclusion hELK x,
        Subgroup.mem_subgroupOf.mpr (hEH (Subgroup.mem_inf.mp x.2).1), rfl⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hELK x ∈ CFSG.pCore 2 K := by
      have h' : QuotientGroup.mk' (CFSG.pCore 2 K) (Subgroup.inclusion hELK x) = 1 :=
        congrArg Subtype.val hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    have h3 : IsPGroup 3 ((E ⊓ L).subgroupOf K) := (hE.isPGroup.to_le inf_le_left).comap_subtype
    have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ h3 CFSG.pCore_isPGroup
    have h2 : Subgroup.inclusion hELK x ∈ (E ⊓ L).subgroupOf K := Subgroup.mem_subgroupOf.mpr x.2
    exact Subgroup.inclusion_injective hELK
      ((Subgroup.disjoint_def.mp hdisj h2 h1).trans (map_one _).symm)
  have hdvd := Subgroup.card_dvd_of_injective φ hinj
  rw [hcard] at hdvd
  have h27 : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
  interval_cases k
  · have : Subsingleton (E ⊓ L : Subgroup G) :=
      (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    exact hEL isCyclic_of_subsingleton
  · exact hEL (isCyclic_of_prime_card (by rw [hk, pow_one]))
  · rw [hk] at hdvd
    norm_num at hdvd
  · rw [hk] at hdvd
    norm_num at hdvd

theorem card_projSU_three_three : Nat.card (projSU 3 3 1) = 6048 :=
  CFSG.PGLModel.card_projSU_three_three

theorem card_of_isSmall194 {X : Type} [Group X] (hX : IsSmall194 X) :
    Nat.card X = 360 ∨ Nat.card X = 6048 := by
  rcases hX with h | h <;> obtain ⟨e⟩ := h
  · left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · right
    rw [Nat.card_congr e.toEquiv, card_projSU_three_three]

theorem not_isSmall194_of_trialityD4
    {X : Type} [Group X]
    (hX : IsSmall194 X) {p f : ℕ}
    (hD4 : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f) : False := by
  obtain ⟨hp, hf, hcard⟩ := card_of_trialityD4 hD4
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  rcases card_of_isSmall194 hX with h | h
  · exact ne_ordTrialityD4 hq (by norm_num) (by norm_num) (by norm_num) (h.symm.trans hcard)
  · exact ne_ordTrialityD4 hq (by norm_num) (by norm_num) (by norm_num) (h.symm.trans hcard)

end Step1911Proof

open Step1911Proof in
theorem step1911_of
    (h194 : Item194Used) :
    Step1911 := by
  intro G _ _ A c L E M hctx K hK hLK hK8 d hdD hdc H hH hHM hKJ
  have hE := hctx.isE27
  have hdE : d ∈ E := (Subgroup.mem_inf.mp hdD).1
  have hEC : E ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdE⟩))
  have hEH : E ≤ H := fun x hx => hH.2 (hEC hx)
  obtain ⟨-, hJ⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJ K hKJ
  refine ⟨?_, ?_⟩
  · rcases hK8 with h | ⟨⟨p, f, hD4⟩, -⟩
    · exact h
    · exact (not_isList194_of_trialityD4 hlist hD4).elim
  · rcases hpar with ⟨-, h⟩ | ⟨-, hext⟩
    · exact h
    · exact (false_of_isExtOf hE hctx.inf_noncyclic hLK hEH hext).elim

open Step1911Proof in
theorem step1911_of_wide
    (h194 : Item194UsedWide) :
    Step1911 := by
  intro G _ _ A c L E M hctx K hK hLK hK8 d hdD hdc H hH hHM hKJ
  have hE := hctx.isE27
  have hdE : d ∈ E := (Subgroup.mem_inf.mp hdD).1
  have hEC : E ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdE⟩))
  have hEH : E ≤ H := fun x hx => hH.2 (hEC hx)
  obtain ⟨-, hJ⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJ K hKJ
  refine ⟨?_, ?_⟩
  · rcases hK8 with h | ⟨⟨p, f, hD4⟩, -⟩
    · exact h
    · rcases hlist with hlist | hsmall
      · exact (not_isList194_of_trialityD4 hlist hD4).elim
      · exact (not_isSmall194_of_trialityD4 hsmall hD4).elim
  · rcases hpar with ⟨-, h⟩ | ⟨-, hext⟩
    · exact h
    · exact (false_of_isExtOf hE hctx.inf_noncyclic hLK hEH hext).elim

end CFSG.RankThree.PartTwo.Sec19
