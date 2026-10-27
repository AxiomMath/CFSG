module

public import CFSG.RankThree.PartOne.K159.AutPair
public import CFSG.Sporadic.Schreier.TitsStab
public import Certificates.Certificate14973

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits

theorem rep_powArr {x : Array ℕ} {σ : Equiv.Perm (Fin 1755)} (hx : Rep 1755 x σ) (k : ℕ) :
    Rep 1755 (powArr x k) (σ ^ k) := by
  induction k with
  | zero => simpa [powArr] using (rep_idA (n := 1755))
  | succ k ih => rw [pow_succ']; exact rep_compA hx ih

theorem autWitness_titsD :
    AutWitness 5 ↥titsD := by
  obtain ⟨hlA, hlB, hlG, hA5, hB5, hAB, hdist, hga, hgb, hmov⟩ :=
    Certificates.certificate14973
  have rA := rep_wordArr_titsT hlA
  have rB := rep_wordArr_titsT hlB
  have rG := rep_wordArr_titsT hlG
  set a := wordIn 13 titsT titsAWord with ha_def
  set b := wordIn 13 titsT titsBWord with hb_def
  set g := wordIn 13 titsT titsGWord with hg_def
  have hpa : ∀ k, Rep 1755 (powArr titsAArr k) (a ^ k) := rep_powArr rA
  have hpb : ∀ k, Rep 1755 (powArr titsBArr k) (b ^ k) := rep_powArr rB
  have hpg : ∀ k, Rep 1755 (powArr titsGArr k) (g ^ k) := rep_powArr rG
  have ha5 : a ^ 5 = 1 := eq_of_eqA (hpa 5) rep_idA hA5
  have hb5 : b ^ 5 = 1 := eq_of_eqA (hpb 5) rep_idA hB5
  have hab : a * b = b * a := eq_of_eqA (rep_compA rA rB) (rep_compA rB rA) hAB
  have hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have h1 := allLt_spec (allLt_spec (allLt_spec (allLt_spec hdist hi) hj) hi') hj'
    have heq : eqA 1755 (pairArr i j) (pairArr i' j') = true :=
      (eqA_iff (rep_compA (hpa i) (hpb j)) (rep_compA (hpa i') (hpb j'))).2 h
    simp only [heq, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1
  have hga' : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j := by
    refine ⟨3, 4, mul_inv_eq_iff_eq_mul.2 ?_⟩
    exact eq_of_eqA (rep_compA rG rA) (rep_compA (rep_compA (hpa 3) (hpb 4)) rG) hga
  have hgb' : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j := by
    refine ⟨2, 4, mul_inv_eq_iff_eq_mul.2 ?_⟩
    exact eq_of_eqA (rep_compA rG rB) (rep_compA (rep_compA (hpa 2) (hpb 4)) rG) hgb
  have hmov' : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → g ^ k * a * (g ^ k)⁻¹ ≠ a := by
    intro k hk1 hk4 h
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 := allLt_spec hmov (show m < 4 by omega)
    have h2 : g ^ (m + 1) * a = a * g ^ (m + 1) := by
      have := mul_inv_eq_iff_eq_mul.1 h
      exact this
    have h3 : eqA 1755 (compA 1755 (powArr titsGArr (m + 1)) titsAArr)
        (compA 1755 titsAArr (powArr titsGArr (m + 1))) = true :=
      (eqA_iff (rep_compA (hpg (m + 1)) rA) (rep_compA rA (hpg (m + 1)))).2 h2
    simp only [h3, Bool.not_true] at h1
    exact Bool.false_ne_true h1
  exact autWitness_of_pair Nat.prime_five titsD (wordIn_titsT_mem_titsD titsAWord)
    (wordIn_titsT_mem_titsD titsBWord) (wordIn_titsT_mem_titsD titsGWord) ha5 hb5 hab hinj hga' hgb'
    hmov'

end CFSG.RankThree.PartOne.K159
