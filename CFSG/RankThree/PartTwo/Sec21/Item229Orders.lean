module

public import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Open (ordBC ordTwistedA)

theorem card_projSL_two (a : ℕ) (ha : 1 ≤ a) :
    Nat.card (projSL 2 (GaloisField 2 a)) = 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
  rw [Nat.card_congr (projSLTwoEquivSL (GaloisField 2 a)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 a (by omega)]

theorem statedClassicalModel_projSp_two {a : ℕ} (ha : 2 ≤ a) :
    StatedClassicalModel (projSp 2 (GaloisField 2 a)) .PSp 2 2 a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, GaloisField 2 a, inferInstance, inferInstance,
    GaloisField.card 2 a (by omega),
    ⟨(CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 (GaloisField 2 a))).symm⟩⟩
  intro h
  have h2 : 2 ^ a = 2 ^ 1 := by
    have := (Prod.mk.inj h).2
    simpa using this
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem card_projSp_two {a : ℕ} (ha : 2 ≤ a) :
    Nat.card (projSp 2 (GaloisField 2 a)) = ordBC 2 (2 ^ a) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two (statedClassicalModel_projSp_two ha)).2.2.1 rfl

theorem statedClassicalModel_projSU {m b : ℕ} (hm : 4 ≤ m) (hb : 1 ≤ b) :
    StatedClassicalModel (projSU m 2 b) .PSU m 2 b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : StatedProj (StatedSU m (2 ^ b) (GaloisField 2 (2 * b))) ≃* projSU m 2 b :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU m 2 b))
  refine ⟨⟨Nat.prime_two, hb, by omega, ?_⟩, GaloisField 2 (2 * b), inferInstance, inferInstance,
    ?_, ⟨e.symm⟩⟩
  · intro h
    have := (Prod.mk.inj h).1
    omega
  · rw [GaloisField.card 2 (2 * b) (by omega), pow_mul, ← pow_mul, mul_comm, pow_mul]

theorem card_projSU {m b : ℕ} (hm : 4 ≤ m) (hb : 1 ≤ b) :
    Nat.card (projSU m 2 b) = ordTwistedA (m - 1) (2 ^ b) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two (statedClassicalModel_projSU hm hb)).2.1 rfl

theorem ordBC_two_eq {a : ℕ} (ha : 1 ≤ a) :
    ordBC 2 (2 ^ a) = (2 ^ a) ^ 4 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 4 - 1)) := by
  have hg : Nat.gcd 2 (2 ^ a - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  rw [ordBC, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num), hg,
    Nat.div_one]

theorem ordTwistedA_three_eq {b : ℕ} (hb : 1 ≤ b) :
    ordTwistedA 3 (2 ^ b) =
      (2 ^ b) ^ 6 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1)) := by
  have hq : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hg : Nat.gcd 4 (2 ^ b + 1) = 1 := by
    have hodd : Odd (2 ^ b + 1) := by
      simpa using CFSG.Timmesfeld.Orders.odd_pow_add_one (f := b) (a := 1) (by omega) one_pos
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  rw [ordTwistedA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl,
    Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide), hg, Nat.div_one,
    show 3 * (3 + 1) / 2 = 6 by rfl, mul_assoc ((2 ^ b) ^ 2 - 1)]

theorem padicValNat_two_pow_mul_odd {k x : ℕ} (hx : Odd x) :
    padicValNat 2 (2 ^ k * x) = k := by
  rw [padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hx.not_two_dvd_nat, add_zero]

theorem padicValNat_pow_two_pow_mul_odd {a k x : ℕ} (hx : Odd x) :
    padicValNat 2 ((2 ^ a) ^ k * x) = a * k := by
  rw [← pow_mul]
  exact padicValNat_two_pow_mul_odd hx

theorem eq_of_mulEquiv_projSL_two {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (e : projSL 2 (GaloisField 2 a) ≃* projSL 2 (GaloisField 2 b)) : a = b := by
  have h := Nat.card_congr e.toEquiv
  rw [card_projSL_two a ha, card_projSL_two b hb] at h
  have hoa : Odd ((2 ^ a) ^ 2 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos
  have hob : Odd ((2 ^ b) ^ 2 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos
  have := congrArg (padicValNat 2) h
  rwa [padicValNat_two_pow_mul_odd hoa, padicValNat_two_pow_mul_odd hob] at this

theorem eq_of_mulEquiv_projSp_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : projSp 2 (GaloisField 2 a) ≃* projSp 2 (GaloisField 2 b)) : a = b := by
  have h := Nat.card_congr e.toEquiv
  rw [card_projSp_two ha, card_projSp_two hb, ordBC_two_eq (by omega), ordBC_two_eq (by omega)]
    at h
  have hoa : Odd (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 4 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have hob : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 4 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have := congrArg (padicValNat 2) h
  rw [padicValNat_pow_two_pow_mul_odd hoa, padicValNat_pow_two_pow_mul_odd hob] at this
  omega

theorem odd_ordTwistedA_three_part {b : ℕ} (hb : 1 ≤ b) :
    Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1)) :=
  ((CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
    (CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))).mul
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))

theorem eq_of_mulEquiv_projSU_four {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (e : projSU 4 2 a ≃* projSU 4 2 b) : a = b := by
  have h := Nat.card_congr e.toEquiv
  rw [card_projSU le_rfl ha, card_projSU le_rfl hb, ordTwistedA_three_eq ha,
    ordTwistedA_three_eq hb] at h
  have := congrArg (padicValNat 2) h
  rw [padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part ha),
    padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part hb)] at this
  omega

theorem not_mulEquiv_projSp_two_projSU_four {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    IsEmpty (projSp 2 (GaloisField 2 a) ≃* projSU 4 2 b) := by
  refine ⟨fun e => ?_⟩
  have h := Nat.card_congr e.toEquiv
  rw [card_projSp_two ha, card_projSU le_rfl hb, ordBC_two_eq (by omega), ordTwistedA_three_eq hb]
    at h
  have hoa : Odd (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 4 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_pow_two_pow_mul_odd hoa,
    padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part hb)] at hv
  obtain ⟨c, rfl, rfl⟩ : ∃ c, a = 3 * c ∧ b = 2 * c := ⟨a / 3, by omega, by omega⟩
  have hpow : ((2 : ℕ) ^ (3 * c)) ^ 4 = (2 ^ (2 * c)) ^ 6 := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  rw [hpow] at h
  have hodd := Nat.eq_of_mul_eq_mul_left (by positivity) h
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = 2 ^ c := ⟨_, rfl⟩
  have hs2 : 2 ≤ s := by
    rw [hs]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℕ) ^ (3 * c) = s ^ 3 := by rw [hs, ← pow_mul, mul_comm]
  have e2 : (2 : ℕ) ^ (2 * c) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
  rw [e1, e2] at hodd
  simp only [← pow_mul] at hodd
  norm_num at hodd
  have h1 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ s ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ s ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4] at hodd
  have hsz : (2 : ℤ) ≤ s := by exact_mod_cast hs2
  have key : ((s : ℤ) ^ 6 - 1) * ((s : ℤ) ^ 12 - 1) -
      ((s : ℤ) ^ 4 - 1) * ((s : ℤ) ^ 6 + 1) * ((s : ℤ) ^ 8 - 1) =
      (s : ℤ) ^ 4 * ((s : ℤ) ^ 6 + 1) * ((s : ℤ) ^ 2 - 1) ^ 2 := by ring
  have hq : (0 : ℤ) < (s : ℤ) ^ 2 - 1 := by nlinarith
  have hpos : (0 : ℤ) < (s : ℤ) ^ 4 * ((s : ℤ) ^ 6 + 1) * ((s : ℤ) ^ 2 - 1) ^ 2 := by
    positivity
  linarith

theorem three_dvd_two_pow_sub_one {n : ℕ} (he : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [← two_mul, pow_mul]
  have h : (4 : ℕ) ^ k ≡ 1 ^ k [MOD 3] := Nat.ModEq.pow k (by decide)
  rw [one_pow] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm

theorem not_isSimpleGroup_SL3 {n : ℕ} (hn : 0 < n) (he : Even n) : ¬ IsSimpleGroup (SL3 n) := by
  intro hs
  have hcard : Nat.card (Subgroup.center (SL3 n)) = 3 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd,
      GaloisField.card 2 n hn.ne']
    exact Nat.gcd_eq_right (three_dvd_two_pow_sub_one he)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (SL3 n)) with h | h
  · rw [h, Subgroup.card_bot] at hcard
    omega
  ·
    let t₁ : SL3 n := ⟨Matrix.transvection 0 1 1, Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩
    let t₂ : SL3 n := ⟨Matrix.transvection 1 0 1, Matrix.det_transvection_of_ne 1 0 (by decide) 1⟩
    have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top t₁) t₂
    have h00 := congrArg (fun g : SL3 n => (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) 0 0) hc
    change (Matrix.transvection (1 : Fin 3) 0 (1 : GaloisField 2 n) *
        Matrix.transvection (0 : Fin 3) 1 (1 : GaloisField 2 n)) 0 0 =
      (Matrix.transvection (0 : Fin 3) 1 (1 : GaloisField 2 n) *
        Matrix.transvection (1 : Fin 3) 0 (1 : GaloisField 2 n)) 0 0 at h00
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h00

end CFSG.RankThree.PartTwo.Sec21
