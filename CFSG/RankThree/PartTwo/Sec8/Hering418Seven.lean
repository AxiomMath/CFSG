module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Orders
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Models.PGLOrders
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Divisibility

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.quotCenter_card_dvd (c : Cfg L K a b) :
    Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))
      ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  refine (card_quot_center_dvd_card c.hKL).trans ?_
  have h1 : (rhoK c.hKL).range ≤ innBar L := by
    rintro _ ⟨k, rfl⟩
    exact rho_mem_innBar L (c.hKL k.2)
  refine (Subgroup.card_dvd_of_le h1).trans ?_
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L))).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem Cfg.sixtyThree_dvd_card (c : Cfg L K a b)
    (hT : Type418Arith (K ⧸ aschbacherSolvableCore 3 K)) :
    63 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have h7 := hT.1.trans c.quotCenter_card_dvd
  have h9 := hT.2.1.trans c.quotCenter_card_dvd
  have : Nat.Coprime 7 (3 ^ 2) := by norm_num
  have h := this.mul_dvd_of_dvd_of_dvd h7 h9
  norm_num at h
  exact h

end Divisibility

section Criterion


theorem kF418ModelOn_of_not_dvd {P : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], P X → ¬ 63 ∣ Nat.card X) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hT := type418Arith_of hn hKq htype
  exact h _ hl (c.sixtyThree_dvd_card hT)

end Criterion

theorem two_pow_mod_seven (m : ℕ) : 2 ^ m % 7 = 2 ^ (m % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_seven_of_not_dvd {m : ℕ} (hm : ¬ 3 ∣ m) :
    2 ^ m % 7 = 2 ∨ 2 ^ m % 7 = 4 := by
  rw [two_pow_mod_seven]
  have : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with h | h <;> rw [h] <;> norm_num

theorem not_seven_dvd_three_pow (e : ℕ) (he : ¬ 3 ∣ e) :
    ¬ 7 ∣ 3 ^ e * ((3 ^ e) ^ 2 - 1) := by
  intro h
  have h7 : Nat.Prime 7 := by norm_num
  rcases (Nat.Prime.dvd_mul h7).mp h with h1 | h1
  · have := (Nat.Prime.dvd_of_dvd_pow h7 h1)
    omega
  · have hpos : 1 ≤ (3 ^ e) ^ 2 := Nat.one_le_pow _ _ (pow_pos (by norm_num) e)
    have hmod : (3 ^ e) ^ 2 % 7 = 1 := by omega
    have h9 : (3 ^ e) ^ 2 = 9 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h9] at hmod
    have h2 : 9 ^ e % 7 = 2 ^ e % 7 := by rw [Nat.pow_mod]
    rw [h2] at hmod
    rcases two_pow_mod_seven_of_not_dvd he with h | h <;> omega

theorem prod_sl_two_div {q : ℕ} (hq : 2 ≤ q) :
    (∏ i : Fin 2, (q ^ 2 - q ^ (i : ℕ))) / (q - 1) = q * (q ^ 2 - 1) := by
  rw [Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hx1 : 1 ≤ q := by omega
  have hxx : q ≤ q ^ 2 := by nlinarith
  have h1q : 1 ≤ q ^ 2 := by nlinarith
  have hmul : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    zify [hx1, hxx, h1q]
    ring
  rw [hmul]
  exact Nat.mul_div_cancel _ (by omega)

theorem card_projSL_two_dvd (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    Nat.card (projSL 2 (GaloisField p e)) ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
  have : Finite (projSL 2 (GaloisField p e)) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 2 (GaloisField p e)).symm.toEquiv
  have hq : 2 ≤ p ^ e :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have h1 := Sec4.card_projSL_dvd 2 (GaloisField p e)
  rwa [card_SL_galoisField 2 p e (by omega), prod_sl_two_div hq] at h1

theorem not_seven_dvd_projSL_two_three (e : ℕ) (he : 1 ≤ e) (h3 : ¬ 3 ∣ e) :
    ¬ 7 ∣ Nat.card (projSL 2 (GaloisField 3 e)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  exact not_seven_dvd_three_pow e h3 (h.trans (card_projSL_two_dvd 3 e he))

section SevenPowers

variable {q : ℕ}

theorem sq_mod_seven (hq : q % 7 = 2 ∨ q % 7 = 4) : q ^ 2 % 7 = 4 ∨ q ^ 2 % 7 = 2 := by
  rw [Nat.pow_mod]
  rcases hq with h | h <;> rw [h] <;> norm_num

theorem cube_mod_seven (hq : q % 7 = 2 ∨ q % 7 = 4) : q ^ 3 % 7 = 1 := by
  rw [Nat.pow_mod]
  rcases hq with h | h <;> rw [h] <;> norm_num

theorem fourth_mod_seven (hq : q % 7 = 2 ∨ q % 7 = 4) : q ^ 4 % 7 = 2 ∨ q ^ 4 % 7 = 4 := by
  rw [Nat.pow_mod]
  rcases hq with h | h <;> rw [h] <;> norm_num

theorem not_seven_dvd_of_mod (hq : q % 7 = 2 ∨ q % 7 = 4) : ¬ 7 ∣ q := by omega

theorem not_seven_dvd_pow_of_mod (hq : q % 7 = 2 ∨ q % 7 = 4) (k : ℕ) : ¬ 7 ∣ q ^ k := fun h =>
  not_seven_dvd_of_mod hq (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)

theorem not_seven_dvd_sp_four (hq : q % 7 = 2 ∨ q % 7 = 4) :
    ¬ 7 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  intro h
  have h7 : Nat.Prime 7 := by norm_num
  have h2 := sq_mod_seven hq
  have h4 := fourth_mod_seven hq
  rcases (Nat.Prime.dvd_mul h7).mp h with h | h
  · exact not_seven_dvd_pow_of_mod hq 4 h
  · rcases (Nat.Prime.dvd_mul h7).mp h with h | h <;> omega

theorem not_seven_dvd_su_three (hq : q % 7 = 2 ∨ q % 7 = 4) :
    ¬ 7 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  intro h
  have h7 : Nat.Prime 7 := by norm_num
  have h2 := sq_mod_seven hq
  have h3 := cube_mod_seven hq
  rcases (Nat.Prime.dvd_mul h7).mp h with h | h
  · exact not_seven_dvd_pow_of_mod hq 3 h
  · rcases (Nat.Prime.dvd_mul h7).mp h with h | h <;> omega

theorem not_seven_dvd_ordTwistedF4 (hq : q % 7 = 2 ∨ q % 7 = 4) (hq2 : 2 ≤ q) :
    ¬ 7 ∣ CFSG.Open.ordTwistedF4 q := by
  intro h
  rw [CFSG.RankThree.PartOne.S12K.ordTwistedF4_eq_factored hq2] at h
  have h7 : Nat.Prime 7 := by norm_num
  have e2 := sq_mod_seven hq
  have e4 := fourth_mod_seven hq
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hq24 : q ^ 2 ≤ q ^ 4 := by nlinarith [Nat.mul_le_mul hqq hqq]
  rcases (Nat.Prime.dvd_mul h7).mp h with h | h
  · rcases (Nat.Prime.dvd_mul h7).mp h with h | h
    · rcases (Nat.Prime.dvd_mul h7).mp h with h | h
      · rcases (Nat.Prime.dvd_mul h7).mp h with h | h
        · rcases (Nat.Prime.dvd_mul h7).mp h with h | h
          · exact not_seven_dvd_pow_of_mod hq 12 h
          · have := Nat.Prime.dvd_of_dvd_pow h7 h
            omega
        · have := Nat.Prime.dvd_of_dvd_pow h7 h
          omega
      · have := Nat.Prime.dvd_of_dvd_pow h7 h
        omega
    · omega
  · omega

end SevenPowers

section Three


@[expose] def IsLTwoThreeNotDvd (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 1 ≤ e ∧ ¬ 3 ∣ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))

theorem kF418ModelOn_L2Three : KF418ModelOn (fun X _ => IsLTwoThreeNotDvd X) := by
  refine kF418ModelOn_of_not_dvd ?_
  intro X _ _ ⟨e, he, h3, ⟨φ⟩⟩ h63
  rw [Nat.card_congr φ.toEquiv] at h63
  exact not_seven_dvd_projSL_two_three e he h3 ((by norm_num : 7 ∣ 63).trans h63)


@[expose] def IsSuzukiTwo (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, Blueprint.SuzukiModel X 2 f

theorem kF418ModelOn_suzuki : KF418ModelOn (fun X _ => IsSuzukiTwo X) := by
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨f, h⟩ h63
  exact KFacts.KP7.three_not_dvd_card h ((by norm_num : 3 ∣ 63).trans h63)

@[expose] def IsTitsTwo (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, Blueprint.ReeTitsModel X .Tits 2 f

theorem kF418ModelOn_tits :
    KF418ModelOn (fun X _ => IsTitsTwo X) := by
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨f, h⟩ h63
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 f h
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD] at h63
  norm_num at h63

@[expose] def IsTwistedF4NotDvd (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, ¬ 3 ∣ f ∧ Blueprint.ReeTitsModel X .twistedF4 2 f

theorem kF418ModelOn_twistedF4 : KF418ModelOn (fun X _ => IsTwistedF4NotDvd X) := by
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨f, hf, h⟩ h63
  have hcard := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
  obtain ⟨-, a, hfa, -⟩ := h
  rw [hcard] at h63
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact not_seven_dvd_ordTwistedF4 (two_pow_mod_seven_of_not_dvd hf) hq2
    ((by norm_num : 7 ∣ 63).trans h63)

@[expose] def IsSpFourNotDvd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ¬ 3 ∣ k ∧ Nonempty (X ≃* projSp 2 (GaloisField 2 k))

theorem kF418ModelOn_spFour : KF418ModelOn (fun X _ => IsSpFourNotDvd X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨k, hk, h3, ⟨φ⟩⟩ h63
  rw [Nat.card_congr φ.toEquiv, CFSG.PGLModel.card_projSp_of_charTwo,
    GaloisField.card 2 k (by omega)] at h63
  have h7 := (by norm_num : 7 ∣ 63).trans h63
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)] at h7
  have e : (2 ^ k) ^ 2 ^ 2 * (((2 ^ k) ^ (2 * 1) - 1) * ((2 ^ k) ^ (2 * 2) - 1)) =
      (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
    norm_num
  rw [e] at h7
  exact not_seven_dvd_sp_four (two_pow_mod_seven_of_not_dvd h3) h7

@[expose] def IsUThreeNotDvd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ¬ 3 ∣ k ∧ Nonempty (X ≃* projSU 3 2 k)

theorem kF418ModelOn_uThree : KF418ModelOn (fun X _ => IsUThreeNotDvd X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨k, hk, h3, ⟨φ⟩⟩ h63
  rw [Nat.card_congr φ.toEquiv] at h63
  have h7 := (by norm_num : 7 ∣ 63).trans h63
  have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 k hk
  have h7' : 7 ∣ (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1)) :=
    hc ▸ Dvd.dvd.mul_right h7 _
  exact not_seven_dvd_su_three (two_pow_mod_seven_of_not_dvd h3) h7'

@[expose] def IsSUThreeNotDvd (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ¬ 3 ∣ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = (2 ^ n) ^ 2 ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K)

theorem kF418ModelOn_suThree : KF418ModelOn (fun X _ => IsSUThreeNotDvd X) := by
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨n, hn, h3, K, _, _, hK, ⟨φ⟩⟩ h63
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  rw [Nat.card_congr φ.toEquiv] at h63
  have h7 := (by norm_num : 7 ∣ 63).trans h63
  have hc := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three hU
  have hc' : Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
    rw [show CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K =
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 3 from rfl, hc, mul_assoc]
  rw [hc'] at h7
  exact not_seven_dvd_su_three (two_pow_mod_seven_of_not_dvd h3) h7


@[expose] def IsLTwoTwoOne (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 2 (GaloisField 2 1))

theorem kF418ModelOn_L2TwoOne : KF418ModelOn (fun X _ => IsLTwoTwoOne X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨φ⟩ h63
  rw [Nat.card_congr φ.toEquiv] at h63
  have h := h63.trans (card_projSL_two_dvd 2 1 le_rfl)
  norm_num at h

@[expose] def IsUFourNotDvd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ¬ 3 ∣ k ∧ Nonempty (X ≃* projSU 4 2 k)

theorem not_seven_dvd_projSU_four {k : ℕ} (hk : 1 ≤ k) (h3 : ¬ 3 ∣ k) :
    ¬ 7 ∣ Nat.card (projSU 4 2 k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 k hk
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 4 (2 ^ k) (GaloisField 2 (2 * k))) :=
    Subtype.finite
  intro h
  have h1 := h.trans (Sec4.card_projSU_dvd 4 2 k)
  have hz := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
  have h1' : (7 : ℤ) ∣ (Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 4 (2 ^ k)
      (GaloisField 2 (2 * k))) : ℤ) := Int.natCast_dvd_natCast.mpr h1
  rw [hz, show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)] at h1'
  have hz7 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h1'
  have hq : ((2 ^ k : ℕ) : ZMod 7) = 2 ∨ ((2 ^ k : ℕ) : ZMod 7) = 4 := by
    have h24 := two_pow_mod_seven_of_not_dvd h3
    have hc : ((2 ^ k : ℕ) : ZMod 7) = ((2 ^ k % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod _ 7).symm
    rcases h24 with h | h <;> rw [hc, h] <;> simp
  push_cast at hz7
  rcases hq with hq | hq <;> push_cast at hq <;> simp only [hq] at hz7 <;> revert hz7 <;> decide


theorem kF418ModelOn_uFour : KF418ModelOn (fun X _ => IsUFourNotDvd X) := by
  refine kF418ModelOn_of_not_dvd ?_
  rintro X _ _ ⟨k, hk, h3, ⟨φ⟩⟩ h63
  rw [Nat.card_congr φ.toEquiv] at h63
  exact not_seven_dvd_projSU_four hk h3 ((by norm_num : 7 ∣ 63).trans h63)

end Three

end CFSG.RankThree.PartTwo.Sec8.Hering418
