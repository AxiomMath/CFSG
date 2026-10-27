module

public import CFSG.RankThree.PartOne.Q1327T.R8Small
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133

theorem units_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (c : Kˣ) :
    c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.1 h1.le
  exact Subsingleton.elim c 1

theorem row8U3Concl_of_small_model {Q : Type} [Group Q] [Finite Q] {p g : ℕ} {Ē : Subgroup Q}
    (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (M : Subgroup (GL ι K))
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj M) (hn : Fintype.card ι ≤ 11) :
    Row8U3Concl g Q Ē := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := h.five_le
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  refine false_of_row8_small hK M (ce.trans e) hp5 h.p_dvd (d := 1)
    (fun c _ => by rw [units_eq_one_of_card_two hK c, one_pow])
    (fun hd => by have := Nat.le_of_dvd one_pos hd; omega) h.elem h.card
    (fun D hD hDc hĒD => by simpa [hZ] using h.max D hD hDc hĒD) hW hn

theorem card_multiplier_psl_two {n : ℕ} (hn : 5 ≤ n) (hn7 : n ≤ 7) :
    Nat.card (Blueprint.Multiplier.generic .PSL n 2 1 ×
      Blueprint.Multiplier.exceptional .PSL n 2 1) = 1 := by
  interval_cases n <;>
  simp [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional,
    Blueprint.Multiplier.genericOrders, Blueprint.Multiplier.exceptionalOrders]

theorem not_dvd_of_dvd_four {p N : ℕ} (hp5 : 5 ≤ p) (hN : N ∣ 4) : ¬ p ∣ N := fun h => by
  have := Nat.le_of_dvd (by norm_num) (h.trans hN)
  omega

theorem not_sq_dvd_of_primeFactors {N : ℕ} (hN : N ≠ 0) (S : Finset ℕ)
    (hS : N.primeFactors = S) (h2 : ∀ p ∈ S, 5 ≤ p → ¬ p ^ 2 ∣ N) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : ¬ p ^ 2 ∣ N := by
  intro h
  have hpN : p ∣ N := (dvd_pow_self p (by norm_num)).trans h
  have : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpN, hN⟩
  rw [hS] at this
  exact h2 p this h5 h

end CFSG.RankThree.PartOne.Q1327T.R8

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133 TauCeti
  CFSG.RankThree.PartOne.Census3

theorem row8U3At_leaf9_linear {m : ℕ} (hm4 : 4 ≤ m) (hm6 : m ≤ 6)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {Q : Type} [Group Q] [Finite Q] {p g : ℕ} {Ē : Subgroup Q} {q : PrimePower}
    (hq2 : q.p = 2) (hq1 : q.exponent = 1)
    (hX : IsoLie (Q ⧸ Subgroup.center Q) (.A m q)) (h : Row8Conf p g Q Ē) :
    Row8U3Concl g Q Ē := by
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  rw [hq2, hq1] at hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .PSL) (n := m + 1)
      (f := 1) ⟨hmod.1, Or.inl hmod⟩ fun hdvd => by
        rw [R8.card_multiplier_psl_two (by omega) (by omega)] at hdvd
        have := Nat.le_of_dvd one_pos hdvd
        have := h.five_le
        omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  exact R8.row8U3Concl_of_small_model h hZ (by simpa using hK) _ e (by simp; omega)

theorem row8U3At_leaf9_zero
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 0) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hiso⟩ := hX
  exact row8U3At_leaf9_linear (m := 4) (by omega) (by omega) hGA hq2 hq1 hiso h

theorem row8U3At_leaf9_one
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 1) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hiso⟩ := hX
  exact row8U3At_leaf9_linear (m := 5) (by omega) (by omega) hGA hq2 hq1 hiso h

theorem row8U3At_leaf9_two
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 2) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hiso⟩ := hX
  exact row8U3At_leaf9_linear (m := 6) (by omega) (by omega) hGA hq2 hq1 hiso h

theorem row8U3At_leaf9_three : Row8U3At (K133.leaf9 3) := by
  intro Q _ _ p g Ē hX h
  exfalso
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e0
  rw [hq2, hq1] at hmod
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  have hdvd : p ^ 2 ∣ Nat.card (Q ⧸ Subgroup.center Q) := hAcard ▸ Subgroup.card_subgroup_dvd_card A
  rw [hcard] at hdvd
  exact R8.not_sq_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 11} (by decide +kernel)
    (by decide) hp hp5 hdvd

theorem row8U3At_leaf9_four
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 4) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2
    (by omega) e0
  rw [hq2, hq1] at hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .PSp) (n := 4)
      (f := 1) ⟨hmod.1, Or.inl hmod⟩ (R8.not_dvd_of_dvd_four h.five_le
        ((KFU.card_multiplier_psp_dvd_two (n := 4) (f := 1) le_rfl).trans (by norm_num)))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  exact R8.row8U3Concl_of_small_model h hZ (by simpa using hK) _ e (by simp)

theorem row8U3At_leaf9_five
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 5) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hq2 e0
  rw [hq2, hq1] at hmod
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier h.prime hGA h.quasisimple h.center_p (t := .POmegaPlus) (n := 4)
      (f := 1) ⟨hmod.1, Or.inl hmod⟩ (R8.not_dvd_of_dvd_four h.five_le
        (KFU.card_multiplier_pOmegaPlus (n := 4) (f := 1) le_rfl))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  exact R8.row8U3Concl_of_small_model h hZ (by simpa using hK) _ e (by simp)

theorem row8U3Item_nine
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF4 : Row8U3At (K133.leaf9 6)) : Row8U3Item 8 :=
  Row8U3At.of_exists (Q := leaf9) (fun X _ hX => by
    obtain ⟨q, hq, he, h0 | h1 | h2 | h3 | h4 | h5 | h6⟩ := hX
    · exact ⟨0, q, hq, he, h0⟩
    · exact ⟨1, q, hq, he, h1⟩
    · exact ⟨2, q, hq, he, h2⟩
    · exact ⟨3, q, hq, he, h3⟩
    · exact ⟨4, q, hq, he, h4⟩
    · exact ⟨5, q, hq, he, h5⟩
    · exact ⟨6, q, hq, he, h6⟩) (fun i => by
    fin_cases i
    · exact row8U3At_leaf9_zero hGA
    · exact row8U3At_leaf9_one hGA
    · exact row8U3At_leaf9_two hGA
    · exact row8U3At_leaf9_three
    · exact row8U3At_leaf9_four hGA
    · exact row8U3At_leaf9_five hGA
    · exact hF4)

end CFSG.RankThree.PartOne.Q1327T
