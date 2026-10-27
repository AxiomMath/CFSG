module

public import CFSG.RankThree.PartOne.KC.UnitaryLogCalculus
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem exists_lift_pow_eq_one (C : Matrix (Fin n) (Fin n) K) (x : primeFormP h C)
    (hxp : x ^ p = 1) : ∃ u : gramSU h C, u ^ p = 1 ∧ (u : primeFormP h C) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hgp : g ^ p ∈ normOneScalars h (gramSU h C) n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hxp
  obtain ⟨c, hcn, -, hc⟩ := hgp
  have hq : p ^ f = p * p ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    have := h.one_le
    omega
  refine ⟨g ^ (p ^ f + 1), ?_, ?_⟩
  · apply Subtype.ext
    rw [← pow_mul, mul_comm, pow_mul, Subgroup.coe_pow, hc, ← map_pow, Subgroup.coe_one]
    have hc1 : c ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← h.norm_eq_pow, hcn, Units.val_one]
    rw [hc1, map_one]
  · rw [QuotientGroup.mk_pow, pow_succ, hq, pow_mul, hxp, one_pow, one_mul]

theorem truncExp_zero_matrix (hn : 1 ≤ n) : truncExp n (0 : Matrix (Fin n) (Fin n) K) = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  simp [truncExp, Finset.sum_range_succ', pow_succ]

theorem exists_skew_log_of_pow_eq_one (hn : 3 ≤ n) (hnp : n ≤ p) {C : GL (Fin n) K}
    (x : primeFormP h (C : Matrix (Fin n) (Fin n) K)) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ (N : Matrix (Fin n) (Fin n) K) (hN : N ^ n = 0) (hskew : unitaryAdjoint h C N = -N),
      N ≠ 0 ∧ (unitaryExp h hn hnp hN hskew :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) = x := by
  obtain ⟨u, hup, hux⟩ := exists_lift_pow_eq_one h _ x hxp
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set M : Matrix (Fin n) (Fin n) K := ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1
    with hM
  have hMp : M ^ p = 0 := by
    have h1 : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hup]
      rfl
    have h2 : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + M := by
      rw [hM]
      abel
    rw [h2, add_pow_char_of_commute p (Commute.one_left M), one_pow] at h1
    simpa using h1
  have hMn : M ^ n = 0 := matrix_pow_eq_zero_of_isNilpotent ⟨p, hMp⟩
  obtain ⟨hnil, hskew⟩ := KCUnitaryLog.unitaryAdjoint_truncLog_of_mem h C (by omega) hnp u.2
    ⟨p, hMp⟩
  have hN : (truncLog n ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ n = 0 :=
    matrix_pow_eq_zero_of_isNilpotent hnil
  have hexp : truncExp n (truncLog n ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    truncExp_truncLog (by omega) (KCUnitaryLog.hK_of_le h hnp) hMn
  have hux' : unitaryExp h hn hnp hN hskew = u := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_unitaryExp]
    exact hexp
  refine ⟨_, hN, hskew, ?_, by rw [hux']; exact hux⟩
  intro hN0
  apply hx1
  rw [← hux]
  have hu1 : u = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hexp, hN0, truncExp_zero_matrix (by omega)]
    rfl
  rw [hu1]
  rfl

end CFSG.RankThree.PartOne.KCUnitaryDefining
