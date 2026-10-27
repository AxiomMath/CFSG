module

public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJComp
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour
import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Multipliers.Tits
import CFSG.Alternating.Multipliers.Small
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate120
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import Certificates.Certificate10009
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3Proof419
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import Certificates.Certificate17002
public import Certificates.Certificate17951
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp StatedSU)
open CFSG.Blueprint
open CFSG.LieType.Steinberg.CentralExt (griessHopfMultiplierCongr)

namespace Item89Res2

theorem injective_of_card_dvd_six {P R : Type} [Group P] [Finite P] [Group R] (f : P →* R)
    (hf : Function.Surjective f) (hP : Group.IsPerfect P) (hker : f.ker ≤ Subgroup.center P)
    (hcop : Nat.Coprime (Nat.card f.ker) 6)
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier R) ∣ 6) : Function.Injective f := by
  have h1 := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hP f hf hker
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess R).toEquiv] at h1
  have h2 : Nat.card f.ker = 1 := Nat.Coprime.eq_one_of_dvd hcop (h1.trans hM)
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.mp h2

theorem card_griessHopfMultiplier_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) = Nat.card (CFSG.Open.griessHopfMultiplier Y) :=
  Nat.card_congr (griessHopfMultiplierCongr e).toEquiv

theorem card_dvd_six_of_subsingleton {X : Type} [Group X]
    (h : Subsingleton (CFSG.Open.griessHopfMultiplier X)) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 6 := by
  rw [Nat.card_unique]
  exact one_dvd _

theorem card_multiplicative_zmod {k : ℕ} (hk : 1 ≤ k) : Nat.card (Multiplicative (ZMod k)) = k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

section Types


theorem card_griessHopfMultiplier_dvd_six {R : Type} [Group R] (h : Sec4.IsType419Theta R)
    (hR : Group.IsPerfect R) : Nat.card (CFSG.Open.griessHopfMultiplier R) ∣ 6 := by
  rcases h with ⟨n, hG2⟩ | ⟨⟨e⟩⟩ | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    obtain ⟨⟨-, hn1, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ := hG2
    rw [card_griessHopfMultiplier_congr e]
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by
        rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
        · norm_num at h3
        · rfl
      subst hn2
      rw [(CFSG.LieType.Steinberg.CentralExt.GriessExceptional.g2_four_card_griessHopfMultiplier
        (by rw [hK]; norm_num)).2]
      norm_num
    · have h5 : 5 ≤ Nat.card K := by
        rw [hK]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      exact card_dvd_six_of_subsingleton
        (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier h5).2
  ·
    rw [card_griessHopfMultiplier_congr (e.trans (Sec4.projSUEquivStatedProj 3 3 1))]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 (2 * 1) (by norm_num)]
      norm_num
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
      (p := 3) (f := 1) hF le_rfl (n := 3) le_rfl (by decide) (by decide)
    rw [Nat.card_congr eM.toEquiv, card_multiplicative_zmod (by norm_num)]
    norm_num
  ·
    have hF4c := hF4
    obtain ⟨⟨-, -, -, -, hodd, h3⟩, a, ha, -⟩ := hF4c
    subst ha
    have hL : CFSG.Blueprint.LieModel R .twistedF4 0 2 (2 * a + 1) :=
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hF4⟩))
    exact card_dvd_six_of_subsingleton
      (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.reeF4_hopfMultiplier (by omega) hL).2
  ·
    have hL : CFSG.Blueprint.LieModel R .Tits 0 2 1 := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hT⟩))
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_Tits R hL
    rw [Nat.card_congr eM.toEquiv, Nat.card_unique]
    exact one_dvd _
  ·
    rw [card_griessHopfMultiplier_congr (e.trans (Sec4.projSpEquivStatedProj 2 _))]
    have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier
      (K := GaloisField 2 n) hK (by omega) le_rfl (fun _ => hn)
    rw [Nat.card_congr eM.toEquiv, hK]
    have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hnd : ¬ 2 ∣ 2 ^ n - 1 := by
        rintro ⟨k, hk⟩
        omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd
    rw [hg, card_multiplicative_zmod le_rfl]
    exact one_dvd _
  ·
    rw [card_griessHopfMultiplier_congr e,
      Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2]
  ·
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    ·
      exfalso
      obtain rfl : m = 1 := by
        obtain ⟨k, rfl⟩ := hm
        omega
      have hcard : Nat.card R = 72 := by
        rw [Nat.card_congr e.toEquiv]
        exact Sec4.Item419ThetaProof.card_projSU_three_two_one
      have : Finite R := Nat.finite_of_card_ne_zero (by omega)
      have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      have hs : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
      exact Sec4.Item419ThetaProof.not_isSolvable_of_isPerfect hR
        (Group.isSolvable_of_isSolvable_injective (f := (e.toMonoidHom : R →* projSU 3 2 1))
          e.injective)
    · rw [card_griessHopfMultiplier_congr (e.trans (Sec4.projSUEquivStatedProj 3 2 m))]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hF : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
        rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
      have hq : (3, 2 ^ m) ≠ (3, 2) := by
        intro h
        have h' : 2 ^ m = 2 ^ 1 := by simpa using h
        have := Nat.pow_right_injective le_rfl h'
        omega
      obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
        (p := 2) (f := m) hF (by omega) (n := 3) le_rfl (by decide) hq
      rw [Nat.card_congr eM.toEquiv,
        card_multiplicative_zmod (Nat.pos_of_ne_zero (by
          intro h0
          rw [Nat.gcd_eq_zero_iff] at h0
          omega))]
      exact (Nat.gcd_dvd_left 3 _).trans (by norm_num)

end Types

end Item89Res2


theorem kF89JMult_holds : KF89JMult := by
  intro P R _ _ _ f hf hP hker hcop htype
  have hR : Group.IsPerfect R := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := f) hf
  exact Item89Res2.injective_of_card_dvd_six f hf hP hker hcop
    (Item89Res2.card_griessHopfMultiplier_dvd_six htype hR)

end CFSG.RankThree.PartTwo.Sec8
