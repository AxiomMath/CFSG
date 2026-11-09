
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Mathlib.GroupTheory.Perm.Centralizer
import Certificates.Kernel.Census.CatFacts.C2014K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum Equiv Equiv.Perm

theorem cycleType_invS8 {s : Perm (Fin 8)} (hs : s * s = 1) :
    s.cycleType = Multiset.replicate (s.support.card / 2) 2 := by
  have h2 : s ^ 2 = 1 := by rw [sq]; exact hs
  have h := cycleType_of_pow_prime_eq_one (p := 2) h2
  have hsum := sum_cycleType s
  rw [h, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [h]
  congr 1
  omega

theorem card_odd_inv8 {s : Perm (Fin 8)} (hs : s * s = 1) (hA : s ∉ alternatingGroup (Fin 8)) :
    s.support.card = 2 ∨ s.support.card = 6 := by
  have hc := cycleType_invS8 hs
  have hsign : Perm.sign s = -1 := by
    rcases Int.units_eq_one_or (Perm.sign s) with h | h
    · exact absurd (mem_alternatingGroup.2 h) hA
    · exact h
  rw [sign_of_cycleType, hc, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hle : s.support.card ≤ 8 := (Finset.card_le_univ _).trans (by simp)
  have hev : s.support.card % 2 = 0 := by
    have h := congrArg Multiset.sum hc
    rw [sum_cycleType, Multiset.sum_replicate, smul_eq_mul] at h
    omega
  obtain ⟨k, hk⟩ : ∃ k, s.support.card = 2 * k := ⟨s.support.card / 2, by omega⟩
  rw [hk, Nat.mul_div_cancel_left k two_pos] at hsign
  rw [hk]
  have hk4 : k ≤ 4 := by omega
  interval_cases k
  · exact absurd hsign (by decide)
  · exact Or.inl rfl
  · exact absurd hsign (by decide)
  · exact Or.inr rfl
  · exact absurd hsign (by decide)

theorem not_comm_five8 {s x : Perm (Fin 8)} (hs : s * s = 1) (h6 : s.support.card = 6)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) : x * s ≠ s * x := by
  intro hxs
  have hmem : x ∈ Subgroup.centralizer {s} := Subgroup.mem_centralizer_singleton_iff.2 hxs
  have hc : s.cycleType = Multiset.replicate 3 2 := by rw [cycleType_invS8 hs, h6]
  have hcard : Nat.card (Subgroup.centralizer {s}) = 96 := by
    rw [nat_card_centralizer, hc, Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [orderOf_eq_prime hx5 hx1, hcard] at hd
  exact absurd hd (by decide)

theorem adm2014 : admCheck (elemsT QS8) QA8 five8 s8 admConj = true := by
  unfold admCheck
  rw [List.all_eq_true]
  intro s _
  beta_reduce
  simp only [Bool.or_eq_true]
  by_cases hs : s * s = 1
  · by_cases hA : s ∈ alternatingGroup (Fin 8)
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact (mem_iff_sift QA8 QA8_ok s).1 (by rw [QA8_eq]; exact hA)
    · rcases card_odd_inv8 hs hA with h2 | h6
      · obtain ⟨x, y, hxy, rfl⟩ := card_support_eq_two.1 h2
        exact Or.inl (Or.inr (admSwap2014K x y hxy))
      · refine Or.inr (List.all_eq_true.2 fun x hx => ?_)
        unfold five8 at hx
        rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at hx
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        exact not_comm_five8 hs h6 hx.2.1 hx.2.2
  · refine Or.inl (Or.inl (Or.inl ?_))
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    exact hs

theorem pow45_of_pow4 {y : Perm (Fin 8)} (h : y ^ 4 = 1) : y ^ 45 = y := by
  rw [show 45 = 4 * 11 + 1 by rfl, pow_succ, pow_mul, h, one_pow, one_mul]

theorem oddNormal2014 : oddNormalCheck (elemsT QL8) 45 = true := by
  have hL : CFSG.Certificates.ValidSchreier QL8 := ql8_2014K.1
  unfold oddNormalCheck
  rw [List.all_eq_true]
  intro x hx
  have h := List.all_eq_true.1 on2014K x (by rw [← elemsT_eq_elemsV]; exact hx)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true]
  rcases h with (h1 | h4) | ⟨c, hc, hk4, hk1⟩
  · exact Or.inl (Or.inl h1)
  · by_cases h1 : x = 1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (by rw [pow45_of_pow4 h4]; exact h1))
  · refine Or.inr ⟨c, ?_, by rw [pow45_of_pow4 hk4]; exact hk1⟩
    have hs := List.all_eq_true.1 onS2014K c hc
    rw [← sift_eq_siftP] at hs
    exact (mem_elemsT QL8 hL c).2 ((mem_iff_sift QL8 hL c).2 hs)

theorem length_filter_card {l : List (Perm (Fin 8))} (hl : l.Nodup) (q : Perm (Fin 8) → Prop)
    [DecidablePred q] (hq : ∀ x, x ∈ l ↔ q x) (p : Perm (Fin 8) → Prop) [DecidablePred p] :
    (l.filter (fun g => decide (p g))).length = (Finset.univ.filter (fun g => q g ∧ p g)).card := by
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext g
  simp [hq]

theorem s8_swap : s8 = swap 0 1 := List.formPerm_pair 0 1

theorem card_cent_s8 :
    (Finset.univ.filter (fun g : Perm (Fin 8) => g * s8 = s8 * g)).card = 1440 := by
  have hss : s8 * s8 = 1 := by rw [s8_swap, swap_mul_self]
  have hc : s8.cycleType = Multiset.replicate 1 2 := by
    rw [cycleType_invS8 hss, s8_swap, card_support_swap (by decide)]
  have h := nat_card_centralizer s8
  rw [hc, Fintype.card_fin] at h
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      Subgroup.mem_centralizer_singleton_iff (g := s8) (k := g))]
  exact h.trans (by decide)

theorem card_cent_s8_even :
    (Finset.univ.filter (fun g : Perm (Fin 8) => Perm.sign g = 1 ∧ g * s8 = s8 * g)).card = 720 := by
  have hss : s8 * s8 = 1 := by rw [s8_swap, swap_mul_self]
  have hsg : Perm.sign s8 = -1 := by rw [s8_swap, sign_swap (by decide)]
  have hmul : ∀ g : Perm (Fin 8), g * s8 = s8 * g → g * s8 * s8 = s8 * (g * s8) := by
    intro g hg
    rw [mul_assoc, hss, mul_one, hg, ← mul_assoc, hss, one_mul]
  have hinv : ∀ g : Perm (Fin 8), g * s8 * s8 = g := by
    intro g
    rw [mul_assoc, hss, mul_one]
  set C := Finset.univ.filter (fun g : Perm (Fin 8) => g * s8 = s8 * g)
  have hsum := Finset.card_filter_add_card_filter_not (s := C) (fun g => Perm.sign g = 1)
  have hC : C.card = 1440 := card_cent_s8
  have hbij : (C.filter fun g => Perm.sign g = 1).card = (C.filter fun g => ¬Perm.sign g = 1).card := by
    apply Finset.card_nbij' (· * s8) (· * s8)
    · intro g hg
      simp only [C, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hg ⊢
      refine ⟨hmul g hg.1, ?_⟩
      rw [Perm.sign_mul, hg.2, hsg]
      decide
    · intro g hg
      simp only [C, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hg ⊢
      refine ⟨hmul g hg.1, ?_⟩
      rw [Perm.sign_mul, hsg]
      rcases Int.units_eq_one_or (Perm.sign g) with h | h
      · exact absurd h hg.2
      · rw [h]
        decide
    · intro g _
      exact hinv g
    · intro g _
      exact hinv g
  have he : (Finset.univ.filter (fun g : Perm (Fin 8) => Perm.sign g = 1 ∧ g * s8 = s8 * g)) =
      C.filter fun g => Perm.sign g = 1 := by
    ext g
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  rw [he]
  omega

theorem cA2014 : ((elemsT QA8).filter (fun g => decide (g * s8 = s8 * g))).length = 720 := by
  rw [length_filter_card (nodup_elemsT QA8 QA8_ok) (fun x => Perm.sign x = 1)
    (fun x => by rw [mem_elemsT QA8 QA8_ok, QA8_eq]; exact mem_alternatingGroup)]
  exact card_cent_s8_even

theorem cS2014 :((elemsT QS8).filter (fun g => decide (g * s8 = s8 * g))).length = 2 ^ 5 * 45 := by
  rw [length_filter_card (nodup_elemsT QS8 QS8_ok) (fun _ => True)
    (fun x => by rw [mem_elemsT QS8 QS8_ok, QS8_eq]; exact iff_of_true (Subgroup.mem_top x) trivial)]
  simp only [true_and]
  exact card_cent_s8

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in
theorem facts2014 : (admCheck (elemsT QS8) QA8 five8 s8 admConj = true)
    ∧ (QL8.check = true ∧ QL8.orderCertificate = 360)
    ∧ (oddNormalCheck (elemsT QL8) 45 = true)
    ∧ (((elemsT QA8).filter (fun g => decide (g * s8 = s8 * g))).length = 720)
    ∧ (QQ8.check = true ∧ QQ8.orderCertificate = 32)
    ∧ ((elemsT QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
      QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true
    )
    ∧ (((elemsT QS8).filter (fun g => decide (g * s8 = s8 * g))).length = 2 ^ 5 * 45) := by
  refine ⟨adm2014, ql8_2014K, oddNormal2014, cA2014, qq8_2014K, ?_, cS2014⟩
  · rw [elemsT_eq_elemsV]
    exact g08_2014K

end CertificateChecks.KernelCatFacts
