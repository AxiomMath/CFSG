
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2013K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum Equiv Equiv.Perm

theorem cycleType_inv8 {s : Perm (Fin 8)} (hs : s * s = 1) :
    s.cycleType = Multiset.replicate (s.support.card / 2) 2 := by
  have h2 : s ^ 2 = 1 := by rw [sq]; exact hs
  have h := cycleType_of_pow_prime_eq_one (p := 2) h2
  have hsum := sum_cycleType s
  rw [h, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [h]
  congr 1
  omega

@[expose] def repB (r x₁ x₂ : Perm (Fin 8)) : Bool :=
  decide (x₁ ^ 3 = 1) && decide (x₂ ^ 3 = 1) && decide (x₁ * r = r * x₁) &&
    decide (x₂ * r = r * x₂) && decide (x₁ * x₂ * (x₁ * x₂) = 1) && !decide (x₁ * x₂ = 1)

@[expose] def WitP (s : Perm (Fin 8)) : Prop :=
  ∃ x₁ x₂ : Perm (Fin 8), x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧ x₁ * s = s * x₁ ∧ x₂ * s = s * x₂ ∧
    (x₁ * x₂) ^ 315 ≠ 1

theorem witP_of_repB {r x₁ x₂ : Perm (Fin 8)} (h : repB r x₁ x₂ = true) : WitP r := by
  unfold repB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, c1⟩, c2⟩, hsq⟩, hne⟩ := h
  refine ⟨x₁, x₂, h1, h2, c1, c2, ?_⟩
  rw [show 315 = 2 * 157 + 1 by rfl, pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
  exact hne

theorem witP_conj {r : Perm (Fin 8)} (h : WitP r) (g : Perm (Fin 8)) : WitP (g * r * g⁻¹) := by
  obtain ⟨x₁, x₂, h1, h2, c1, c2, h12⟩ := h
  have hφ : ∀ x, MulAut.conj g x = g * x * g⁻¹ := fun x => MulAut.conj_apply g x
  rw [← hφ]
  refine ⟨MulAut.conj g x₁, MulAut.conj g x₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_mul, c1, map_mul]
  · rw [← map_mul, c2, map_mul]
  · rw [← map_mul, ← map_pow, Ne, MulEquiv.map_eq_one_iff]
    exact h12

theorem rep_wit : repB 1 c[5, 6, 7] c[4, 5, 6] = true ∧
    repB (swap 0 1) c[5, 6, 7] c[4, 5, 6] = true ∧
    repB (swap 0 1 * swap 2 3) c[5, 6, 7] c[4, 5, 6] = true ∧
    repB (swap 0 1 * swap 2 3 * swap 4 5) (c[0, 2, 4] * c[1, 3, 5]) (c[0, 4, 3] * c[1, 5, 2]) =
      true ∧
    repB (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) (c[2, 4, 6] * c[3, 5, 7])
      (c[2, 6, 5] * c[3, 7, 4]) = true := by
  decide +kernel

theorem rep_supp : (1 : Perm (Fin 8)).support.card = 0 ∧ (swap (0 : Fin 8) 1).support.card = 2 ∧
    (swap (0 : Fin 8) 1 * swap 2 3).support.card = 4 ∧
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5).support.card = 6 ∧
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7).support.card = 8 := by
  decide +kernel

theorem rep_inv : (swap (0 : Fin 8) 1) * (swap 0 1) = 1 ∧
    (swap (0 : Fin 8) 1 * swap 2 3) * (swap 0 1 * swap 2 3) = 1 ∧
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5) * (swap 0 1 * swap 2 3 * swap 4 5) = 1 ∧
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7) *
      (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) = 1 := by
  decide +kernel

theorem witP_of_rep {s r : Perm (Fin 8)} (hs : s * s = 1) (hr : r * r = 1) (hw : WitP r)
    (hc : r.support.card = s.support.card) : WitP s := by
  have hconj : IsConj r s := by
    rw [isConj_iff_cycleType_eq, cycleType_inv8 hs, cycleType_inv8 hr, hc]
  obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
  exact witP_conj hw g

theorem wit8 {s : Perm (Fin 8)} (hs : s * s = 1) : WitP s := by
  have hle : s.support.card ≤ 8 := (Finset.card_le_univ _).trans (by simp)
  have hev : s.support.card % 2 = 0 := by
    have h := congrArg Multiset.sum (cycleType_inv8 hs)
    rw [sum_cycleType, Multiset.sum_replicate, smul_eq_mul] at h
    omega
  obtain ⟨w0, w1, w2, w3, w4⟩ := rep_wit
  obtain ⟨s0, s1, s2, s3, s4⟩ := rep_supp
  obtain ⟨i1, i2, i3, i4⟩ := rep_inv
  have hcases : s.support.card = 0 ∨ s.support.card = 2 ∨ s.support.card = 4 ∨
      s.support.card = 6 ∨ s.support.card = 8 := by omega
  rcases hcases with h | h | h | h | h
  · exact witP_of_rep hs (mul_one 1) (witP_of_repB w0) (s0.trans h.symm)
  · exact witP_of_rep hs i1 (witP_of_repB w1) (s1.trans h.symm)
  · exact witP_of_rep hs i2 (witP_of_repB w2) (s2.trans h.symm)
  · exact witP_of_rep hs i3 (witP_of_repB w3) (s3.trans h.symm)
  · exact witP_of_rep hs i4 (witP_of_repB w4) (s4.trans h.symm)

theorem mem_odd_of_cube {x : Perm (Fin 8)} (h : x ^ 3 = 1) :
    x ∈ (elemsT QA8).filter oddTest := by
  rw [List.mem_filter, mem_elemsT QA8 QA8_ok, QA8_eq, mem_alternatingGroup]
  refine ⟨?_, ?_⟩
  · have h1 : Perm.sign x ^ 3 = 1 := by rw [← map_pow, h, map_one]
    rcases Int.units_eq_one_or (Perm.sign x) with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  · unfold oddTest
    rw [Bool.or_eq_true, decide_eq_true_eq]
    left
    rw [show 15 = 3 * 5 by rfl, pow_mul, h, one_pow]

theorem noNilp2013 : noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true := by
  unfold noNilpCheck
  rw [List.all_eq_true]
  intro s _
  beta_reduce
  by_cases hs : s * s = 1
  · obtain ⟨x₁, x₂, h1, h2, c1, c2, h12⟩ := wit8 hs
    have hp : pairWitness (((elemsT QA8).filter oddTest).filter fun x => decide (x * s = s * x))
        315 = true := by
      unfold pairWitness
      rw [List.any_eq_true]
      refine ⟨x₁, List.mem_filter.2 ⟨mem_odd_of_cube h1, decide_eq_true c1⟩, ?_⟩
      rw [List.any_eq_true]
      refine ⟨x₂, List.mem_filter.2 ⟨mem_odd_of_cube h2, decide_eq_true c2⟩, ?_⟩
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      exact h12
    rw [hp, Bool.or_true]
  · rw [decide_eq_false hs]
    rfl

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in
theorem facts2013 : (centTrivCheck (elemsT QS8) a8 b8 = true)
    ∧ (noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true) :=
  ⟨by rw [elemsT_eq_elemsV]; exact cent2013K, noNilp2013⟩

end CertificateChecks.KernelCatFacts
