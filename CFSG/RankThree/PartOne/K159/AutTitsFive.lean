module

public import CFSG.RankThree.PartOne.K159.AutPairFive
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.K159.AutTits
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def titsIter : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => (3 * (titsIter k).1 + 2 * (titsIter k).2, 4 * (titsIter k).1 + 4 * (titsIter k).2)

section Pair

variable {G : Type*} [Group G]

theorem conj_pow_eq_titsIter {a b g : G} (hab : a * b = b * a) (hga : g * a * g⁻¹ = a ^ 3 * b ^ 4)
    (hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4) (k : ℕ) :
    g ^ k * a * (g ^ k)⁻¹ = a ^ (titsIter k).1 * b ^ (titsIter k).2 := by
  induction k with
  | zero => simp [titsIter]
  | succ k ih =>
    have hc : Commute a b := hab
    have h1 : g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, ih]
    set x := (titsIter k).1 with hx
    set y := (titsIter k).2 with hy
    have h2 : g * (a ^ x * b ^ y) * g⁻¹ = (g * a * g⁻¹) ^ x * (g * b * g⁻¹) ^ y := by
      rw [conj_pow, conj_pow]
      group
    rw [h2, hga, hgb]
    have e1 : (a ^ 3 * b ^ 4) ^ x = a ^ (3 * x) * b ^ (4 * x) := by
      rw [(Commute.pow_pow hc 3 4).mul_pow, ← pow_mul, ← pow_mul, mul_comm 3 x, mul_comm 4 x]
    have e2 : (a ^ 2 * b ^ 4) ^ y = a ^ (2 * y) * b ^ (4 * y) := by
      rw [(Commute.pow_pow hc 2 4).mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 y, mul_comm 4 y]
    rw [e1, e2]
    calc a ^ (3 * x) * b ^ (4 * x) * (a ^ (2 * y) * b ^ (4 * y))
        = a ^ (3 * x) * (b ^ (4 * x) * a ^ (2 * y)) * b ^ (4 * y) := by group
      _ = a ^ (3 * x) * (a ^ (2 * y) * b ^ (4 * x)) * b ^ (4 * y) := by
          rw [(Commute.pow_pow hc.symm (4 * x) (2 * y)).eq]
      _ = a ^ (3 * x + 2 * y) * b ^ (4 * x + 4 * y) := by
          rw [pow_add, pow_add]
          group

theorem moves_of_tits_pair {a b g : G} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    (hga : g * a * g⁻¹ = a ^ 3 * b ^ 4) (hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 6 → g ^ k * a * (g ^ k)⁻¹ ≠ a := by
  intro k hk1 hk6 h
  rw [conj_pow_eq_titsIter hab hga hgb k] at h
  have h' : a ^ ((titsIter k).1 % 5) * b ^ ((titsIter k).2 % 5) = a ^ 1 * b ^ 0 := by
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_one, pow_zero, mul_one]
    exact h
  have h5 := hinj _ _ 1 0 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (by norm_num) (by norm_num) h'
  interval_cases k <;> simp [titsIter] at h5

end Pair

open CFSG.Sporadic.Schreier.Tits in
theorem autWitnessUpTo_six_titsD :
    AutWitnessUpTo 6 5 ↥titsD := by
  obtain ⟨hlA, hlB, hlG, hA5, hB5, hAB, hdist, hga, hgb, -⟩ :=
    Certificates.certificate14973
  have rA := rep_wordArr_titsT hlA
  have rB := rep_wordArr_titsT hlB
  have rG := rep_wordArr_titsT hlG
  set a := wordIn 13 titsT titsAWord with ha_def
  set b := wordIn 13 titsT titsBWord with hb_def
  set g := wordIn 13 titsT titsGWord with hg_def
  have hpa : ∀ k, Rep 1755 (powArr titsAArr k) (a ^ k) := rep_powArr rA
  have hpb : ∀ k, Rep 1755 (powArr titsBArr k) (b ^ k) := rep_powArr rB
  have ha5 : a ^ 5 = 1 := eq_of_eqA (hpa 5) rep_idA hA5
  have hb5 : b ^ 5 = 1 := eq_of_eqA (rep_powArr rB 5) rep_idA hB5
  have hab : a * b = b * a := eq_of_eqA (rep_compA rA rB) (rep_compA rB rA) hAB
  have hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have h1 := allLt_spec (allLt_spec (allLt_spec (allLt_spec hdist hi) hj) hi') hj'
    have heq : eqA 1755 (pairArr i j) (pairArr i' j') = true :=
      (eqA_iff (rep_compA (hpa i) (hpb j)) (rep_compA (hpa i') (hpb j'))).2 h
    simp only [heq, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1
  have hga3 : g * a * g⁻¹ = a ^ 3 * b ^ 4 :=
    mul_inv_eq_iff_eq_mul.2
      (eq_of_eqA (rep_compA rG rA) (rep_compA (rep_compA (hpa 3) (hpb 4)) rG) hga)
  have hgb2 : g * b * g⁻¹ = a ^ 2 * b ^ 4 :=
    mul_inv_eq_iff_eq_mul.2
      (eq_of_eqA (rep_compA rG rB) (rep_compA (rep_compA (hpa 2) (hpb 4)) rG) hgb)
  exact autWitnessUpTo_of_pair Nat.prime_five titsD (wordIn_titsT_mem_titsD titsAWord)
    (wordIn_titsT_mem_titsD titsBWord) (wordIn_titsT_mem_titsD titsGWord) ha5 hb5 hab hinj
    ⟨3, 4, hga3⟩ ⟨2, 4, hgb2⟩ (moves_of_tits_pair ha5 hb5 hab hinj hga3 hgb2)

theorem autWitnessUpTo_six_of_isoLie_tits
    {S : Type} [Group S] (h : IsoLie S .tits) : AutWitnessUpTo 6 5 S := by
  obtain ⟨e⟩ := titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits h)
  exact AutWitnessUpTo.of_mulEquiv e.symm autWitnessUpTo_six_titsD

end CFSG.RankThree.PartOne.K159
