module

public import CFSG.RankThree.PartOne.Q1327T.Item7F4Inv
import CFSG.RankThree.PartOne.SEITZX.ReeSplit
public import CFSG.RankThree.PartOne.Q1327T.Item7Inv

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.K128
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

open CFSG.RankThree.PartOne.Census3 (IsoLie)


theorem card_multiplier_twistedF4_dvd_one (f : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .twistedF4 0 2 f ×
      Blueprint.Multiplier.exceptional .twistedF4 0 2 f) ∣ 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .twistedF4 0 2 f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .twistedF4 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

set_option linter.unusedSectionVars false

theorem row8U3At_leaf7_nine
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 9) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨m, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := h.elem
  obtain ⟨Xf, _, _, _, hm1, hXc, ⟨eK⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hLie : Models.LieModel (Q ⧸ Subgroup.center Q) .twistedF4 0 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
      Or.inr ⟨rfl, ⟨.reeF4 m, hv⟩, ⟨rfl, rfl⟩, ⟨e0⟩⟩⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p hLie fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) (hd.trans (card_multiplier_twistedF4_dvd_one (2 * m + 1)))
    omega
  refine h.concl_of_inv hZ ?_
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* ReeTag.F4.reeGamma Xf m := ce.trans eK
  refine exists_inv_of_equiv eQ ?_
  have hEel : IsElementaryAbelian p (Ē.map eQ.toMonoidHom) := IsElementaryAbelian.map _
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  have hpg : IsPGroup p (Ē.map eQ.toMonoidHom) := IsElementaryAbelian.isPGroup p _
  have : Finite (ModGL ReeTag.F4.tag Xf) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma Xf m) := Subtype.finite
  have hpΓ : p ∣ Nat.card (ReeTag.F4.reeGamma Xf m) := by
    have h1 := Subgroup.card_subgroup_dvd_card (Ē.map eQ.toMonoidHom)
    rw [hEcard] at h1
    exact (dvd_pow_self p two_ne_zero).trans h1
  rcases (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion m
    Xf hXc).2 p hp (by omega) hpΓ with h1 | h2 | h3 | h4 | h5
  · exact exists_inv_reeGamma hXc (d := 1) (Or.inl rfl) hp hp5 h1 hpg
  · exact exists_inv_reeGamma hXc (d := 2) (Or.inr (Or.inl rfl)) hp hp5 h2 hpg
  · exact exists_inv_reeGamma hXc (d := 4) (Or.inr (Or.inr rfl)) hp hp5 h3 hpg
  · exfalso
    have hrk := pRank_le_one_ree_phi6 hXc hp hp5 h4
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEel hEcard
    omega
  · exfalso
    have hrk := pRank_le_one_ree_phi12 hXc hp hp5 h5
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEel hEcard
    omega

end CFSG.RankThree.PartOne.Q1327T
