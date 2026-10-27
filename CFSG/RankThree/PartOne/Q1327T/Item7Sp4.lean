module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.Q1327T.Item7Weights
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)

theorem row8U3At_leaf7_four
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 4) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
  rw [hq2] at hmod
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p (t := .PSp) (n := 2)
      (f := q.exponent) ⟨hmod.1, Or.inl hmod⟩ fun hdvd => ?_
    have h2 := hdvd.trans (KFU.card_multiplier_psp_dvd_two (n := 2) (f := q.exponent) hmod.1.2.1)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  refine ⟨hZ, fun ⟨φ⟩ => ?_⟩
  exfalso
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 :=
    N143X.natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hdvd := card_dvd_eight_of_matrix_model (StatedSp 2 K) (ce.trans e) hp hp2 hpK (d := 2) ?_
    (fun h2 => by have := Nat.le_of_dvd (by norm_num) h2; omega) (N143X.symJ 2 K)
    (N143X.symJ_det_ne_zero 2 K) (fun g hg => N143X.statedSp_le_isoGroup 2 K hg) h.elem (by simp)
  · have h6 : Nat.card Ē.normalizerMonoidHom.range = 6 := by
      rw [← torusImage_top_eq_range]
      exact (Nat.card_congr φ.toEquiv).trans
        (by simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
    rw [h6] at hdvd
    omega
  · intro c hc
    have hJ := N143X.statedSp_le_isoGroup 2 K hc
    rw [N143X.mem_isoGroup] at hJ
    have h1 := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    simpa [N143X.symJ, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.fromBlocks, Fintype.sum_sum_type] using h1

end CFSG.RankThree.PartOne.Q1327T
