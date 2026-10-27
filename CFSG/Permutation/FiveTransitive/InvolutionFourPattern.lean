module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.InvolutionFourPattern

open Equiv MulAction

theorem exists_two_swaps {X : Type*} [Fintype X] [DecidableEq X]
    (s : Perm X) (hs : orderOf s = 2) (hm : 4 ≤ s.support.card) :
    ∃ e : Fin 4 ↪ X, s (e 0) = e 1 ∧ s (e 1) = e 0 ∧
      s (e 2) = e 3 ∧ s (e 3) = e 2 := by
  have hss (x : X) : s (s x) = x := by
    have hpow := pow_orderOf_eq_one s
    rw [hs, pow_two] at hpow
    exact DFunLike.congr_fun hpow x
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.support.card by omega)
  let b := s a
  have hab : a ≠ b := (Perm.mem_support.mp ha).symm
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ s.support, c ≠ a ∧ c ≠ b := by
    by_contra h
    push Not at h
    have hsub : s.support ⊆ {a, b} := by
      intro x hx
      by_cases he : x = a
      · simp [he]
      · simp [h x hx he]
    have hle := Finset.card_le_card hsub
    have : ({a, b} : Finset X).card = 2 := by simp [hab]
    omega
  let d := s c
  have hcd : c ≠ d := (Perm.mem_support.mp hc).symm
  have hda : d ≠ a := by
    intro he
    have he' := congrArg s he
    have : c = b := by simpa only [d, hss] using he'
    exact hcb this
  have hdb : d ≠ b := fun he => hca (s.injective he)
  let f : Fin 4 → X := ![a,b,c,d]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hab, hab.symm, hca, hca.symm, hcb, hcb.symm, hcd, hcd.symm, hda, hda.symm, hdb, hdb.symm]
  refine ⟨⟨f,hf⟩, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hss a
  · rfl
  · exact hss c

theorem four_dvd_orderOf {X : Type*} [Finite X]
    (r : Perm X) {a b c d : X} (had : a ≠ d)
    (ha : r a = b) (hb : r b = d) (hd : r d = c) (hc : r c = a) :
    4 ∣ orderOf r := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ Function.IsPeriodicPt r (2^1) a := by
    change r (r a) ≠ a
    rw [ha, hb]
    exact had.symm
  have hper : Function.IsPeriodicPt r (2^(1+1)) a := by
    change r (r (r (r a))) = a
    rw [ha, hb, hd, hc]
  have hperiod := Function.minimalPeriod_eq_prime_pow hnot hper
  have horder : Function.IsPeriodicPt r (orderOf r) a := by
    change (r : X → X)^[orderOf r] a = a
    rw [← Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hdiv := horder.minimalPeriod_dvd
  simpa [hperiod] using hdiv

theorem exists_conjugate_pattern {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h4 : IsMultiplyPretransitive P X 4)
    (s : Perm X) (e : Fin 4 ↪ X)
    (hs01 : s (e 0) = e 1) (hs10 : s (e 1) = e 0)
    (hfixed : 2 ≤ (fixedBy X s).ncard) :
    ∃ k : P, let v := (k : Perm X) * s * (k : Perm X)⁻¹
      v (e 0) = e 0 ∧ v (e 3) = e 3 ∧ v (e 1) = e 2 ∧ v (e 2) = e 1 := by
  classical
  have hnF : Nontrivial (fixedBy X s) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_coe_set_eq]
    omega)
  let _ := hnF
  obtain ⟨a,b,hab⟩ := exists_pair_ne (fixedBy X s)
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have ha : s a.val = a.val := a.property
  have hb : s b.val = b.val := b.property
  have he01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have ha0 : a.val ≠ e 0 := by intro h; have := ha; rw [h,hs01] at this; exact he01 this.symm
  have ha1 : a.val ≠ e 1 := by intro h; have := ha; rw [h,hs10] at this; exact he01 this
  have hb0 : b.val ≠ e 0 := by intro h; have := hb; rw [h,hs01] at this; exact he01 this.symm
  have hb1 : b.val ≠ e 1 := by intro h; have := hb; rw [h,hs10] at this; exact he01 this
  let f : Fin 4 → X := ![a.val,b.val,e 0,e 1]
  let z : Fin 4 → X := ![e 0,e 3,e 1,e 2]
  have hf : Function.Injective f := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [f,hab',ha0,ha1,hb0,hb1,he01,eq_comm]
  have hz : Function.Injective z := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals have he := e.injective h
    all_goals omega
  obtain ⟨k,hk⟩ := isMultiplyPretransitive_iff.mp h4 (⟨f,hf⟩ : Fin 4 ↪ X) ⟨z,hz⟩
  have hk0 : (k : Perm X) a.val = e 0 := DFunLike.congr_fun hk 0
  have hk1 : (k : Perm X) b.val = e 3 := DFunLike.congr_fun hk 1
  have hk2 : (k : Perm X) (e 0) = e 1 := DFunLike.congr_fun hk 2
  have hk3 : (k : Perm X) (e 1) = e 2 := DFunLike.congr_fun hk 3
  have hinv (x : X) : (k : Perm X)⁻¹ ((k : Perm X) x) = x := (k : Perm X).symm_apply_apply x
  have hi0 : (k : Perm X)⁻¹ (e 0) = a.val := by rw [← hk0, hinv]
  have hi1 : (k : Perm X)⁻¹ (e 3) = b.val := by rw [← hk1, hinv]
  have hi2 : (k : Perm X)⁻¹ (e 1) = e 0 := by rw [← hk2, hinv]
  have hi3 : (k : Perm X)⁻¹ (e 2) = e 1 := by rw [← hk3, hinv]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simpa only [Perm.mul_apply, hi0, ha] using hk0
  · simpa only [Perm.mul_apply, hi1, hb] using hk1
  · simpa only [Perm.mul_apply, hi2, hs01] using hk3
  · simpa only [Perm.mul_apply, hi3, hs10] using hk2

end FiveTransitive.InvolutionFourPattern

end CFSG
