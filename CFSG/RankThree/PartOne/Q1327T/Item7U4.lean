module

public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)

theorem row8U3At_leaf7_six
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 6) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 4 2 q.exponent := by
    have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
    rw [hq2] at this
    exact this
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hmod
  have hf : 1 ≤ q.exponent := q.exponent_pos
  generalize q.exponent = f at hmod hK e hf
  have hcenter : 2 ≤ f → Subgroup.center Q = ⊥ := fun hf2 => by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p (t := .PSU) (n := 4)
      (f := f) ⟨hmod.1, Or.inl hmod⟩ fun hdvd => ?_
    rw [card_multiplier_psu_eq (Or.inr hf2)] at hdvd
    have := Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left 4 _))
    omega
  by_cases hpq1 : p ∣ 2 ^ f + 1
  · exfalso
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      have := Nat.le_of_dvd (by norm_num) hpq1
      omega
    have hZ := hcenter hf2
    obtain ⟨π, hπ, hπk⟩ := exists_cover_unitary hZ e
    have hker : ¬ p ∣ Nat.card π.ker := by
      rw [hπk, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
        (by norm_num : 1 ≤ 4)).2.2]
      intro hd
      have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 4 _))
      omega
    exact false_of_unitary_diag hp (le_refl 4) hf hK hpq1 π hπ hker hZ h.elem h.card h.max
  · by_cases hpq2 : p ∣ 2 ^ f - 1
    · have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        have := Nat.le_of_dvd (by norm_num) hpq2
        omega
      have hZ := hcenter hf2
      refine ⟨hZ, fun ⟨φ⟩ => ?_⟩
      exfalso
      let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
      have hdvd := card_dvd_eight_of_unitary (n := 4) hp hp2 (by norm_num) (by norm_num) hf hK
        hpq2 (ce.trans e) h.elem
      have h6 : Nat.card Ē.normalizerMonoidHom.range = 6 := by
        rw [← torusImage_top_eq_range]
        exact (Nat.card_congr φ.toEquiv).trans
          (by simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
      rw [h6] at hdvd
      omega
    · exfalso
      have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have hpQ : ¬ p ∣ 2 ^ f := fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      have hd3 := three_le_orderOf_neg_of_not_dvd hp hpQ hpq2 hpq1 hq1
      have hrk := pRank_statedProj_statedSU_le_one (n := 4) hp hp2 (by norm_num) hK hpq1
        (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
      have h2 := h.two_le_pRank
      rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at h2
      omega

end CFSG.RankThree.PartOne.Q1327T
