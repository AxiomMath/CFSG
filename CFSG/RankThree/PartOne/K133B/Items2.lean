module

public import CFSG.RankThree.PartOne.K133B.Weights
public import CFSG.RankThree.PartOne.K133B.PGroup
public import CFSG.RankThree.PartOne.Q1327F.Unip
public import CFSG.RankThree.PartOne.Q1327F.Orders
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.Q1327T CFSG.RankThree.PartOne.Q1327F
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedSp)

theorem row8OddConcl_of_matrix_four {Q : Type} [Group Q] [Finite Q] {p g : ℕ} {Ē : Subgroup Q}
    (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (M : Subgroup (GL ι K))
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj M) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hpK : (p : K) ≠ 0) (hι : Fintype.card ι ≤ 4) : Row8OddConcl p Q Ē := by
  intro _
  have : Fact p.Prime := ⟨h.prime⟩
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact oddOrderOneOrThree_of_matrix_four M (ce.trans e) hd hpd hpK h.elem
    (fun D hD hDc hĒD => by simpa [hZ] using h.max D hD hDc hĒD) hι

theorem row8OddConcl_of_matrix_four_prime {Q : Type} [Group Q] [Finite Q] {p g ℓ : ℕ}
    {Ē : Subgroup Q} (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥) (hℓ : ℓ.Prime)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K]
    [CharP K ℓ] (M : Subgroup (GL ι K)) (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj M) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hι : Fintype.card ι ≤ 4) (hcube : p = ℓ → p ^ 3 ∣ Nat.card (StatedProj M)) :
    Row8OddConcl p Q Ē := by
  intro hW
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpr : p = ℓ
  · exfalso
    subst hpr
    let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    refine false_of_pGroup_plane' hZ ?_ ?_ h.elem h.card
      (fun F hF hFc hEF => by simpa [hZ] using h.max F hF hFc hEF) hW
    · intro y ⟨k, hk⟩
      have h1 : ((ce.trans e) y) ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
      have h2 := statedProj_pow_p_eq_one (ι := ι) (by omega) M _ ⟨k, h1⟩
      exact (map_eq_one_iff _ (ce.trans e).injective).1 (by rw [map_pow]; exact h2)
    · rw [Nat.card_congr (ce.trans e).toEquiv]
      exact hcube rfl
  · have hpK : (p : K) ≠ 0 := fun h0 =>
      hpr ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 ((CharP.cast_eq_zero_iff K ℓ p).1 h0)).symm
    exact row8OddConcl_of_matrix_four h hZ M e hd hpd hpK hι hW

theorem scalar_pow_of_mem_statedSU {n q : ℕ} {K : Type} [Field K] (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q K) : c ^ n = 1 :=
  N143X.pow_eq_one_of_scalar_det (N143X.det_eq_one_of_mem_statedSU' hc)

theorem scalar_pow_of_mem_statedSL {n : ℕ} {K : Type} [Field K] (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K) : c ^ n = 1 :=
  N143X.pow_eq_one_of_scalar_det (N143X.det_eq_one_of_mem_statedSL' hc)

theorem scalar_sq_of_mem_statedSp {K : Type} [Field K] (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ StatedSp 2 K) : c ^ 2 = 1 := by
  have hJ := N143X.statedSp_le_isoGroup 2 K hc
  rw [N143X.mem_isoGroup] at hJ
  have h1 := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
  simpa [N143X.symJ, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.fromBlocks, Fintype.sum_sum_type] using h1

theorem not_dvd_small {p d : ℕ} (hp5 : 5 ≤ p) (hd : d ≤ 4) (hd0 : d ≠ 0) : ¬ p ∣ d := fun h => by
  have := Nat.le_of_dvd (by omega) h
  omega

section Even

theorem row8OddAt_leaf7_two : Row8OddAt (K133.leaf7 2) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 2 q.exponent := by
    have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e0
    rw [hq2] at this
    exact this
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 := N143X.natCast_ne_zero_of_card_two_pow (g := 2 * q.exponent)
    (by rw [hK, ← pow_mul, mul_comm]) hp (by omega)
  exact row8OddConcl_of_matrix_four h hZ (StatedSU 3 (2 ^ q.exponent) K) e (d := 3)
    (fun c hc => scalar_pow_of_mem_statedSU c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) hpK (by simp)

theorem row8OddAt_leaf7_three : Row8OddAt (K133.leaf7 3) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 2 q.exponent := by
    have := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2] at this
    exact this
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 :=
    N143X.natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  exact row8OddConcl_of_matrix_four h hZ (StatedSL 3 K) e (d := 3)
    (fun c hc => scalar_pow_of_mem_statedSL c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) hpK (by simp)

theorem row8OddAt_leaf7_four : Row8OddAt (K133.leaf7 4) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
  rw [hq2] at hmod
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 :=
    N143X.natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  exact row8OddConcl_of_matrix_four h hZ (StatedSp 2 K) e (d := 2)
    (fun c hc => scalar_sq_of_mem_statedSp c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) hpK (by simp)

theorem row8OddAt_leaf7_six : Row8OddAt (K133.leaf7 6) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 4 2 q.exponent := by
    have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
    rw [hq2] at this
    exact this
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 := N143X.natCast_ne_zero_of_card_two_pow (g := 2 * q.exponent)
    (by rw [hK, ← pow_mul, mul_comm]) hp (by omega)
  exact row8OddConcl_of_matrix_four h hZ (StatedSU 4 (2 ^ q.exponent) K) e (d := 4)
    (fun c hc => scalar_pow_of_mem_statedSU c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) hpK (by simp)

theorem row8OddAt_leaf8_zero : Row8OddAt (K133.leaf8 0) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 4 2 q.exponent := by
    have := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2] at this
    exact this
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 :=
    N143X.natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  exact row8OddConcl_of_matrix_four h hZ (StatedSL 4 K) e (d := 4)
    (fun c hc => scalar_pow_of_mem_statedSL c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) hpK (by simp)

end Even

section Odd

theorem row8OddAt_leaf4_one : Row8OddAt (K133.leaf4 1) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e0
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKc : Nat.card K = q.p := by rw [hK, hq1, pow_one]
  have hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK
  exact row8OddConcl_of_matrix_four_prime h hZ q.prime_p (StatedSp 2 K) e (d := 2)
    (fun c hc => scalar_sq_of_mem_statedSp c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) (by simp) (fun hpr => p_cube_dvd_card_psp_two hp (by rw [hKc, hpr]))

theorem row8OddAt_leaf4_three : Row8OddAt (K133.leaf4 3) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 4 q.p q.exponent :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKc : Nat.card K = q.p := by rw [hK, hq1, pow_one]
  have hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK
  exact row8OddConcl_of_matrix_four_prime h hZ q.prime_p (StatedSL 4 K) e (d := 4)
    (fun c hc => scalar_pow_of_mem_statedSL c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) (by simp) (fun hpr => p_cube_dvd_card_psl_four hp (by rw [hKc, hpr]))

theorem row8OddAt_leaf4_two : Row8OddAt (K133.leaf4 2) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 4 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hK1 : Nat.card K = (q.p ^ 1) ^ 2 := by rw [hK, hq1]
  have e1 : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSU 4 (q.p ^ 1) K) := hq1 ▸ e
  have hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      (k := 2) (by norm_num) (by rw [hK1]; ring)
  exact row8OddConcl_of_matrix_four_prime h hZ q.prime_p (StatedSU 4 (q.p ^ 1) K) e1 (d := 4)
    (fun c hc => scalar_pow_of_mem_statedSU c hc) (not_dvd_small (by omega) (by norm_num)
      (by norm_num)) (by simp)
    (fun hpr => by rw [hpr]; exact p_cube_dvd_card_psu_four q.prime_p hK1)

end Odd

end CFSG.RankThree.PartOne.K133B
