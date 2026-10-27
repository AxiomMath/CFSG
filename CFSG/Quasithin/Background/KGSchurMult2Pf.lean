module

public import CFSG.Quasithin.Background.KGSchurMult2
public import CFSG.Sporadic.Recognition.M22MultiplierCert
public import CFSG.Sporadic.Recognition.M23MultiplierCert
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.Sporadic.Recognition.J4Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
public import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import Certificates.Certificate15042
public import Certificates.Certificate15043

public section

namespace CFSG.Quasithin

namespace SchurMult2

theorem isPerfect {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) : Group.IsPerfect K :=
  Group.isPerfect_def.2 hK.1

theorem card_center_dvd {K X : Type} [Group K] [Group X] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X) :
    Nat.card ↥(Subgroup.center K) ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv]
  exact CFSG.GH74.Generic.card_center_dvd_hopfMultiplier
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK) e

theorem eq_bot_of_dvd_odd {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(Subgroup.center K))
    {m : ℕ} (hm : Odd m) (h : Nat.card ↥(Subgroup.center K) ∣ m) : Subgroup.center K = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at h ⊢
  rcases k with _ | k
  · rfl
  · exfalso
    obtain ⟨c, rfl⟩ := (pow_dvd_pow 2 (Nat.succ_le_succ (Nat.zero_le k))).trans h
    rw [pow_one] at hm
    exact Nat.not_even_iff_odd.2 hm (even_two_mul c)

theorem card_dvd_of_dvd_mul_odd {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 2 ↥(Subgroup.center K)) {a m : ℕ} (hm : Odd m)
    (h : Nat.card ↥(Subgroup.center K) ∣ 2 ^ a * m) : Nat.card ↥(Subgroup.center K) ∣ 2 ^ a := by
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at h ⊢
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).dvd_of_dvd_mul_right h

theorem card_generic_prod_exceptional (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) =
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_center_dvd_row {K X : Type} [Group K] [Group X] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
      CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f)) :
    Nat.card ↥(Subgroup.center K) ∣
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨m⟩⟩ := h
  rw [← card_generic_prod_exceptional, ← Nat.card_congr m.toEquiv]
  exact card_center_dvd hK e

theorem eq_bot_of_subsingleton {K X : Type} [Group K] [Group X] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X)
    (h : Subsingleton (CFSG.Open.griessHopfMultiplier X)) : Subgroup.center K = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one ?_)
  have := card_center_dvd hK e
  rwa [@Nat.card_of_subsingleton _ (1 : CFSG.Open.griessHopfMultiplier X) h] at this

theorem eq_bot_of_noPerfectDoubleCover {K X : Type} [Group K] [Group X] [Finite K]
    (hX : CFSG.Monster.Schur.NoPerfectDoubleCover X) (hK : CFSG.Open.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(Subgroup.center K)) (e : K ⧸ Subgroup.center K ≃* X) :
    Subgroup.center K = ⊥ :=
  eq_bot_of_dvd_odd hZ
    (CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover hX K
      hK.1 ⟨e⟩) dvd_rfl

end SchurMult2

open SchurMult2

theorem schurMult2M22_holds :
    SchurMult2M22 := by
  intro K _ _ hK hZ ⟨e⟩
  obtain ⟨hcyc, hdvd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate
      (isPerfect hK) e
  exact ⟨hcyc, card_dvd_of_dvd_mul_odd hZ (a := 2) (m := 3) (by decide) (by simpa using hdvd)⟩

theorem schurMult2M23_holds :
    SchurMult2M23 := by
  intro K _ _ hK _ ⟨e⟩
  exact Subgroup.eq_bot_of_card_eq _
    (CFSG.Sporadic.Recognition.M23Multiplier.card_center_eq_one_of_certificate (isPerfect hK) e)

theorem schurMult2M24_holds :
    SchurMult2M24 := by
  intro K _ _ hK hZ ⟨e⟩
  exact eq_bot_of_noPerfectDoubleCover CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24 hK hZ e

theorem schurMult2J4_holds :
    SchurMult2J4 := by
  intro K _ _ hK hZ ⟨e⟩
  exact eq_bot_of_noPerfectDoubleCover
    (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
      Certificates.certificate15042 Certificates.certificate15043) hK hZ e

theorem schurMult2He_holds :
    SchurMult2He := fun K _ _ hK _ hs =>
  CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate K
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK) hs

theorem schurMult2L32_holds :
    SchurMult2L32 := by
  intro K _ _ hK _ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  simpa [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]
    using this

theorem schurMult2L34_holds :
    SchurMult2L34 := by
  intro K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  simp only [CFSG.Blueprint.Multiplier.genericOrders,
    CFSG.Blueprint.Multiplier.exceptionalOrders] at this
  exact card_dvd_of_dvd_mul_odd hZ (a := 4) (m := 3) (by decide) (by simpa using this)

theorem schurMult2L3_holds :
    SchurMult2L3 := by
  intro n hn K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 n = (1, 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rfl
  rw [he] at this
  simp only [CFSG.Blueprint.Multiplier.genericOrders, mul_one] at this
  exact eq_bot_of_dvd_odd hZ (Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)) this

theorem schurMult2L42_holds :
    SchurMult2L42 := by
  intro K _ _ hK _ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  simpa [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]
    using this

theorem schurMult2L52_holds :
    SchurMult2L52 := by
  intro K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  refine eq_bot_of_dvd_odd hZ (m := 1) (by decide) ?_
  simpa [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]
    using this

theorem schurMult2Sp4_holds :
    SchurMult2Sp4 := by
  intro n K _ _ hK hZ h
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hf, -, h22⟩, -⟩ := id h
    by_contra hlt
    exact h22 (by rw [show n = 1 by omega]; rfl)
  have hq : 5 ≤ 2 ^ n ∨ 2 ^ n = 4 ∨ (2 ^ n = 2 ∧ 4 ≤ 2) ∨ (2 ^ n = 3 ∧ 3 ≤ 2) := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ((show 5 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) h3))
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row h hq)
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  rw [he] at this
  simp only [CFSG.Blueprint.Multiplier.genericOrders, mul_one] at this
  refine eq_bot_of_dvd_odd hZ (Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right 2 _)) this
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one

theorem schurMult2U4_holds :
    SchurMult2U4 := by
  intro n hn K _ _ hK hZ h
  have hq : 4 ≤ 2 ^ n ∨ (2 ^ n = 2 ∧ 8 ≤ 4) ∨ (2 ^ n = 3 ∧ 6 ≤ 4) :=
    Or.inl ((show 4 ≤ 2 ^ 2 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) hn))
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row h (by decide) hq)
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 n = (1, 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rfl
  rw [he] at this
  simp only [CFSG.Blueprint.Multiplier.genericOrders, mul_one] at this
  refine eq_bot_of_dvd_odd hZ (Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right 4 _)) this
  exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one

theorem schurMult2U5_holds :
    SchurMult2U5 := by
  intro n K _ _ hK hZ h
  have := card_center_dvd_row hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row h (by decide))
  rw [CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSU_odd (n := 5)
    (by decide)] at this
  simp only [CFSG.Blueprint.Multiplier.genericOrders, mul_one] at this
  exact eq_bot_of_dvd_odd hZ (Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 5 _)) this

theorem schurMult2G2_holds :
    SchurMult2G2 := by
  intro n hn K _ _ hK _ h
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  refine eq_bot_of_subsingleton hK e
    (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier ?_).2
  rw [hF]
  exact (show 5 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) hn)

theorem schurMult2G24_holds :
    SchurMult2G24 := by
  intro K _ _ hK hZ h
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨hperf, hle⟩ :=
    CFSG.LieType.Steinberg.CentralExt.G2Four.g2_four_hopfMultiplier (hF.trans (by norm_num))
  have : Finite (CFSG.Blueprint.AdjointQuotient .G2 F) :=
    Finite.of_surjective _ (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have : Finite (CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .G2 F)) := by
    have := CFSG.RankThree.PerfectCover.finite_hopfMultiplier (Group.isPerfect_def.2 hperf)
    exact Finite.of_equiv _
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  have hle2 : Nat.card ↥(Subgroup.center K) ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (card_center_dvd hK e)).trans hle
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hle2 ⊢
  have hk1 : k ≤ 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hle2.trans_eq (pow_one 2).symm)
  simpa using pow_dvd_pow 2 hk1

theorem schurMult2D4_holds :
    SchurMult2D4 := by
  intro n K _ _ hK _ h
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, σ, hσ, ⟨e⟩⟩ := h
  exact eq_bot_of_subsingleton hK e
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.triality_hopfMultiplier
      (Nat.le_self_pow (by omega) 2) hF hσ).2

theorem schurMult2F4_holds :
    SchurMult2F4 := by
  intro n K _ _ hK _ h
  have hR := h
  obtain ⟨⟨-, -, -, -, -, h3⟩, a, rfl, -⟩ := h
  refine eq_bot_of_subsingleton hK (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.reeF4_hopfMultiplier (m := a)
      (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩)))).2

theorem schurMultTwoTable_holds :
    SchurMultTwoTable :=
  ⟨schurMult2M22_holds, schurMult2M23_holds, schurMult2M24_holds, schurMult2J4_holds,
    schurMult2He_holds, schurMult2L32_holds, schurMult2L34_holds, schurMult2L3_holds,
    schurMult2L42_holds, schurMult2L52_holds, schurMult2Sp4_holds, schurMult2G24_holds,
    schurMult2G2_holds, schurMult2D4_holds, schurMult2F4_holds, schurMult2U4_holds,
    schurMult2U5_holds⟩

end CFSG.Quasithin
