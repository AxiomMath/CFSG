module

public import CFSG.RankThree.PartOne.Q1327T.R8Small
public import CFSG.RankThree.PartOne.Q1327T.R8Weir
public import CFSG.RankThree.PartOne.Q1327T.R8Orth
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133 TauCeti
  CFSG.RankThree.PartOne.Census3

theorem card_multiplier_psl_four_dvd_two {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSL 4 2 f ×
      Blueprint.Multiplier.exceptional .PSL 4 2 f) ∣ 2 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL 4 2 f = (Nat.gcd 4 (2 ^ f - 1), 1) := rfl
  have hodd : Nat.gcd 4 (2 ^ f - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hm : (2 ^ f - 1) % 2 = 1 := by omega
    have hc2 : Nat.Coprime 2 (2 ^ f - 1) := Nat.coprime_two_left.2 (Nat.odd_iff.2 hm)
    simpa using Nat.Coprime.pow_left 2 hc2
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 4 2 f = (2, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .PSL 4 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hodd]
  rcases hexc with h | h <;> rw [h] <;> simp

theorem not_dvd_of_dvd_two' {p N : ℕ} (hp5 : 5 ≤ p) (hN : N ∣ 2) : ¬ p ∣ N := fun h => by
  have := Nat.le_of_dvd (by norm_num) (h.trans hN)
  omega

theorem scalar_pow_one_of_bot {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] (M : Subgroup (GL ι K)) (hbot : (StatedScalars ι K).subgroupOf M = ⊥) (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar ι c ∈ M) : c ^ 1 = 1 := by
  have hmem : (⟨Matrix.GeneralLinearGroup.scalar ι c, hc⟩ : ↥M) ∈
      (StatedScalars ι K).subgroupOf M := ⟨c, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : Matrix.GeneralLinearGroup.scalar ι c = 1 := congrArg Subtype.val hmem
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h2 := congrArg (fun A : GL ι K => ((A : GL ι K) : Matrix ι ι K) i i) h1
  simp [Matrix.GeneralLinearGroup.coe_scalar] at h2
  rw [pow_one]
  exact Units.ext (by simpa using h2)

theorem scalar_pow_four_of_mem_statedSL {K : Type} [Field K] (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 K) : c ^ 4 = 1 := by
  have h1 := N143X.det_eq_one_of_mem_statedSL' hc
  have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = (c : K) ^ 4 := by
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [h2] at h1
  exact Units.ext (by simpa using h1)

theorem exists_lifted_plane {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {Q : Type} [Group Q] [Finite Q] {p g : ℕ}
    {Ē : Subgroup Q} (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥)
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj M) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d) :
    ∃ F : Subgroup (GL ι K), IsElementaryAbelian p F ∧ F ≤ M ∧ Nat.card F = p ^ 2 ∧
      ∀ D : Subgroup (GL ι K), D ≤ M → IsElementaryAbelian p D → F ≤ D →
        D ≤ Subgroup.centralizer (F : Set (GL ι K)) → Nat.card D ≤ Nat.card F := by
  have : Fact p.Prime := ⟨h.prime⟩
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨F, eF, hFel, hFM, hFmax, -⟩ := exists_lifted_conf M (ce.trans e) hd hpd h.elem
    (fun D hD hDc hĒD => by simpa [hZ] using h.max D hD hDc hĒD)
  refine ⟨F, hFel, hFM, ?_, hFmax⟩
  rw [Nat.card_congr eF.toEquiv]
  exact h.card

end CFSG.RankThree.PartOne.Q1327T.R8

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133 TauCeti
  CFSG.RankThree.PartOne.Census3

theorem row8U3At_leaf8_one
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf8 1) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
    (by norm_num) e0
  rw [hq2] at hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .PSp) (n := 3)
      (f := q.exponent) ⟨hmod.1, Or.inl hmod⟩ (R8.not_dvd_of_dvd_two' hp5
        (KFU.card_multiplier_psp_dvd_two (n := 3) (f := q.exponent) q.exponent_pos))
  refine ⟨hZ, fun _ => ?_⟩
  exfalso
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hchar : CharP K 2 := N143X.charP_two_of_card hK
  have hbot := KFU.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := 3) (by norm_num)
  obtain ⟨F, hFel, hFM, hFc, hFmax⟩ := R8.exists_lifted_plane (StatedSp 3 K) h hZ e (d := 1)
    (fun c hc => R8.scalar_pow_one_of_bot _ hbot c hc)
    (fun hd => by have := Nat.le_of_dvd one_pos hd; omega)
  have := hFel
  exact R8.false_of_plane_sp6 hK hp5 F hFM hFc hFmax

theorem row8U3At_leaf8_two
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf8 2) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hq2 e0
  rw [hq2] at hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .POmegaMinus) (n := 4)
      (f := q.exponent) ⟨hmod.1, Or.inl hmod⟩ (by
        rw [KFU.card_multiplier_pOmegaMinus (n := 4) (f := q.exponent) q.exponent_pos
          (by norm_num)]
        intro hd
        have := Nat.le_of_dvd one_pos hd
        omega)
  refine ⟨hZ, fun _ => ?_⟩
  exfalso
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

theorem row8U3At_leaf8_zero
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf8 0) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  rw [hq2] at hmod
  have hmod' : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 4 2 q.exponent := hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .PSL) (n := 4)
      (f := q.exponent) ⟨hmod'.1, Or.inl hmod'⟩ (R8.not_dvd_of_dvd_two' hp5
        (R8.card_multiplier_psl_four_dvd_two q.exponent_pos))
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod'
  have hchar : CharP K 2 := N143X.charP_two_of_card hK
  have hpd : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  obtain ⟨F, hFel, hFM, hFc, hFmax⟩ := R8.exists_lifted_plane (StatedSL 4 K) h hZ e (d := 4)
    (fun c hc => R8.scalar_pow_four_of_mem_statedSL c hc) hpd
  have := hFel
  by_cases he2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2
  ·
    let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    obtain ⟨m, u, hu, hm0, hmn, hm3, hmo⟩ := R8.row8_weight_numbers hK (StatedSL 4 K)
      (ce.trans e) hp5 (d := 4) (fun c hc => R8.scalar_pow_four_of_mem_statedSL c hc) hpd h.elem
      h.card (fun D hD hDc hĒD => by simpa [hZ] using h.max D hD hDc hĒD) hW
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_units, hu, ← hK]
      exact he2
    rw [hu2] at hmo
    simp only [Fintype.card_fin] at hmn
    omega
  · exact R8.false_of_plane_sl4 hK hp5 F hFM hFc hFmax he2

theorem row8U3Item_seven
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3Item 7 :=
  Row8U3At.of_exists (Q := leaf8) (fun X _ hX => by
    obtain ⟨q, hq, h0 | h1 | h2⟩ := hX
    · exact ⟨0, q, hq, h0⟩
    · exact ⟨1, q, hq, h1⟩
    · exact ⟨2, q, hq, h2⟩) (fun i => by
    fin_cases i
    · exact row8U3At_leaf8_zero hGA
    · exact row8U3At_leaf8_one hGA
    · exact row8U3At_leaf8_two hGA)

end CFSG.RankThree.PartOne.Q1327T
