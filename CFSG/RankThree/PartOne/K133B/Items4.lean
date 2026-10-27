module

public import CFSG.RankThree.PartOne.Q1327T.R8Item8
import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.Q1327T TauCeti CFSG.RankThree.PartOne.Census3
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU StatedSp StatedSL
  StatedOmega StatedQuadMinus)

theorem row8OddAt_leaf8_one : Row8OddAt (K133.leaf8 1) := by
  intro Q _ _ p g Ē hp11 hZ hX h _
  exfalso
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
    (by norm_num) e0
  rw [hq2] at hmod
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hchar : CharP K 2 := N143X.charP_two_of_card hK
  have hbot := KFU.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := 3) (by norm_num)
  obtain ⟨F, hFel, hFM, hFc, hFmax⟩ := R8.exists_lifted_plane (StatedSp 3 K) h hZ e (d := 1)
    (fun c hc => R8.scalar_pow_one_of_bot _ hbot c hc)
    (fun hd => by have := Nat.le_of_dvd one_pos hd; omega)
  have := hFel
  exact R8.false_of_plane_sp6 hK hp5 F hFM hFc hFmax

theorem row8OddAt_leaf8_two : Row8OddAt (K133.leaf8 2) := by
  intro Q _ _ p g Ē hp11 hZ hX h _
  exfalso
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hq2 e0
  rw [hq2] at hmod
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmod
  have hchar : CharP K 2 := N143X.charP_two_of_card hK
  have hbot := KFU.statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot (K := K) (b := b)
    (c := c)
  obtain ⟨F, hFel, hFM, hFc, hFmax⟩ := R8.exists_lifted_plane
    (StatedOmega (StatedQuadMinus 4 K b c)) h hZ e (d := 1)
    (fun c hc => R8.scalar_pow_one_of_bot _ hbot c hc)
    (fun hd => by have := Nat.le_of_dvd one_pos hd; omega)
  have := hFel
  exact R8.false_of_plane_omegaMinus8 hK hirr hp5 F hFM hFc hFmax

theorem row8OddAt_leaf7_seven : Row8OddAt (K133.leaf7 7) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp2 : p ≠ 2 := by omega
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 5 2 q.exponent := by
    have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e0
    rw [hq2] at this
    exact this
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hmod
  have hf : 1 ≤ q.exponent := q.exponent_pos
  generalize q.exponent = f at hmod hK e hf
  by_cases hpq1 : p ∣ 2 ^ f + 1
  · intro _
    exfalso
    have hp5' : p ≠ 5 := by omega
    have hn5 : ¬ p ∣ 5 := fun hd =>
      hp5' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd)
    obtain ⟨π, hπ, hπk⟩ := exists_cover_unitary hZ e
    have hker : ¬ p ∣ Nat.card π.ker := by
      rw [hπk, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
        (by norm_num : 1 ≤ 5)).2.2]
      exact fun hd => hn5 (hd.trans (Nat.gcd_dvd_left 5 _))
    exact false_of_unitary_diag hp (by norm_num : 4 ≤ 5) hf hK hpq1 π hπ hker hZ h.elem h.card
      h.max
  · by_cases hpq2 : p ∣ 2 ^ f - 1
    · intro _
      let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
      have hdvd := card_dvd_eight_of_unitary (n := 5) hp hp2 (by norm_num) (by norm_num) hf hK
        hpq2 (ce.trans e) h.elem
      rw [← torusImage_top_eq_range] at hdvd
      exact OddOrderOneOrThree.of_card_dvd (a := 3) (hdvd.trans (by norm_num))
    · intro _
      exfalso
      have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have hpQ : ¬ p ∣ 2 ^ f := fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      have hd3 := three_le_orderOf_neg_of_not_dvd hp hpQ hpq2 hpq1 hq1
      have hrk := pRank_statedProj_statedSU_le_one (n := 5) hp hp2 (by norm_num) hK hpq1
        (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
      have h2 := h.two_le_pRank
      rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at h2
      omega

end CFSG.RankThree.PartOne.K133B
