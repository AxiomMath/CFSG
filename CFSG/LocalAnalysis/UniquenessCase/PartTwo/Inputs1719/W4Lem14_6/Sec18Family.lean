module

public import CFSG.Adapters.LieModelOrders
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStart
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D4
public import CFSG.Quasithin.Background.PushS3Klein
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
open CFSG.GH74.Uniqueness.Bender (BenderType)


private theorem le_dMinDeg_of_ppd {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    {p k : ℕ} (hp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (hdvd : p ∣ Nat.card L) :
    k ≤ dMinDeg L := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  haveI : Nontrivial L := hL.toNontrivial
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := L) p hdvd
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.le_dMinDeg (fun d f hf => ?_)
  have hker : f.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hf
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hord : orderOf (f s) = p := by rw [orderOf_injective f hinj s, hs]
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.le_of_orderOf_eq_ppd hp hk (f s) hord

theorem dMinDeg_lower_bounds {L : Type} [Group L] [Finite L] {n : ℕ} :
    (IsL2 L n → 2 ≤ n → dMinDeg L = 2 * n) ∧
    (IsSz L n → 4 * n ≤ dMinDeg L) ∧ (IsSp4 L n → 1 < n → 4 * n ≤ dMinDeg L) ∧
      (IsG2 L n → 1 < n → 6 * n ≤ dMinDeg L) ∧ (IsU4 L n → 1 < n → 6 * n ≤ dMinDeg L) ∧
      (LieModel L .PSU 5 2 2 → 20 ≤ dMinDeg L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hL2 hn2
    obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hL2
    exact CFSG.LocalAnalysis.WeakClosure81.dMinDeg_eq_of_mulEquiv_sl2 hn2
      (e.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)))
  · intro hSz
    haveI hs : IsSimpleGroup L := uc22p22r_lieModel_isSimple_twistedB2 hSz
    have hn3 : 3 ≤ n := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
    have hcard : Nat.card L = CFSG.Open.ordSuzuki (2 ^ n) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 hSz
    obtain ⟨p, hp⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (4 * n) (by omega) (by omega)
    have hp' : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (4 * n) := hp
    have hpadd : p ∣ (2 ^ n) ^ 2 + 1 := by
      have h := (hp'.dvd_add_one_iff (by omega) (2 * n)).mpr
        ⟨⟨1, by ring⟩, by
          intro hc
          have hle := Nat.le_of_dvd (by omega : 0 < 2 * n) hc
          omega⟩
      rwa [show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [mul_comm, pow_mul]] at h
    have hdvd : p ∣ Nat.card L := by
      rw [hcard]
      show p ∣ (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpadd ((2 ^ n) ^ 2)) (2 ^ n - 1)
    exact le_dMinDeg_of_ppd hs hp' (by omega) hdvd
  · intro hSp hn1
    haveI hs : IsSimpleGroup L :=
      uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl rfl))) hSp
    have hcard : Nat.card L = CFSG.Open.ordBC 2 (2 ^ n) := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0) hSp]
      rfl
    obtain ⟨p, hp⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (4 * n) (by omega) (by omega)
    have hp' : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (4 * n) := hp
    have hp4 : p ∣ (2 ^ n) ^ 4 - 1 := by
      have h := hp'.dvd
      rwa [show 2 ^ (4 * n) = (2 ^ n) ^ 4 by rw [mul_comm, pow_mul]] at h
    have hdvd : p ∣ Nat.card L := by
      rw [hcard, CFSG.Timmesfeld.Orders.ordBC_two_eq (g := n) (by omega)]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hp4 ((2 ^ n) ^ 2 - 1)) (2 ^ (n * 4))
    exact le_dMinDeg_of_ppd hs hp' (by omega) hdvd
  · intro hG2 hn1
    haveI hs : IsSimpleGroup L := uc22p22r_lieModel_isSimple_G2 hG2
    have hcard : Nat.card L = CFSG.Open.ordG2 (2 ^ n) := by
      have hce := hG2.chevalleyExceptionalModel (t := .G2) (by decide)
      simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hce
    obtain ⟨p, hp⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (6 * n) (by omega) (by omega)
    have hp' : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (6 * n) := hp
    have hp6 : p ∣ (2 ^ n) ^ 6 - 1 := by
      have h := hp'.dvd
      rwa [show 2 ^ (6 * n) = (2 ^ n) ^ 6 by rw [mul_comm, pow_mul]] at h
    have hdvd : p ∣ Nat.card L := by
      rw [hcard, CFSG.Timmesfeld.Orders.ordG2_eq (f := n)]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hp6 ((2 ^ n) ^ 2 - 1)) (2 ^ (n * 6))
    exact le_dMinDeg_of_ppd hs hp' (by omega) hdvd
  · intro hU4 hn1
    haveI hs : IsSimpleGroup L :=
      uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hU4
    have hcard : Nat.card L = CFSG.Open.ordTwistedA 3 (2 ^ n) := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0) hU4]
      rfl
    obtain ⟨p, hp⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (6 * n) (by omega) (by omega)
    have hp' : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (6 * n) := hp
    have hp3 : p ∣ (2 ^ n) ^ 3 + 1 := by
      have h := (hp'.dvd_add_one_iff (by omega) (3 * n)).mpr
        ⟨⟨1, by ring⟩, by
          intro hc
          have hle := Nat.le_of_dvd (by omega : 0 < 3 * n) hc
          omega⟩
      rwa [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by rw [mul_comm, pow_mul]] at h
    have hdvd : p ∣ Nat.card L := by
      rw [hcard, CFSG.RankThree.PartTwo.Sec21.ordTwistedA_three_eq (b := n) (by omega)]
      exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp3 ((2 ^ n) ^ 2 - 1)) ((2 ^ n) ^ 4 - 1))
        ((2 ^ n) ^ 6)
    exact le_dMinDeg_of_ppd hs hp' (by omega) hdvd
  · intro hU5
    haveI hs : IsSimpleGroup L :=
      uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hU5
    have hcard : Nat.card L = CFSG.Open.ordTwistedA 4 (2 ^ 2) := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : (5 : ℕ) ≠ 0) hU5]
      rfl
    have hp41 : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 41 20 :=
      ⟨by norm_num, by norm_num, by
        intro j hj0 hj
        interval_cases j <;> norm_num⟩
    have hdvd : 41 ∣ Nat.card L := by
      rw [hcard]
      decide
    exact le_dMinDeg_of_ppd hs hp41 (by norm_num) hdvd

theorem exists_benderType_of_shape {L : Type} [Group L] {n : ℕ} (hn : 2 < n)
    (hshape : IsL2 L n ∨ IsSz L n) : ∃ i e, BenderType L n i e ∧ i ≠ 3 := by
  rcases hshape with hL2 | hSz
  · obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hL2
    exact ⟨1, 1, BenderType.linear n (by omega) e, by norm_num⟩
  · obtain ⟨a, ha, hfa, hb⟩ :=
      CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_twistedB2 hSz
    exact ⟨2, 1, by simpa [← hfa] using hb, by norm_num⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
