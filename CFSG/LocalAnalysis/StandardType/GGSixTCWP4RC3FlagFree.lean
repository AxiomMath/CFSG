
module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFive
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFlag

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes

section FlagFree

private theorem tch_E_order_four {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {q : K}
    (hq : orderOf q = 4) (m : ℕ) :
    (q ^ m = 1 ↔ m % 4 = 0) ∧ (q ^ m = -1 ↔ m % 4 = 2) := by
  have h4 : q ^ 4 = 1 := by
    rw [← hq]
    exact pow_orderOf_eq_one q
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hq] at hd
    norm_num at hd
  have hsq : q ^ 2 = -1 := by
    have hprod : (q ^ 2 - 1) * (q ^ 2 + 1) = 0 := by
      have e : (q ^ 2 - 1) * (q ^ 2 + 1) = q ^ 4 - 1 := by ring
      rw [e, h4, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hq2
    · linear_combination h
  have hq1 : q ≠ 1 := by
    intro h
    apply hq2
    rw [h, one_pow]
  have hqm1 : q ≠ -1 := by
    intro h
    apply hq2
    rw [h, neg_one_sq]
  have hm1 : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hm1' : (-1 : K) ≠ 1 := fun h => hm1 h.symm
  have hq3 : q ^ 3 = -q := by
    rw [(by ring : q ^ 3 = q ^ 2 * q), hsq, neg_one_mul]
  have hq3a : q ^ 3 ≠ 1 := by
    intro h
    apply hqm1
    linear_combination hq3 - h
  have hq3b : q ^ 3 ≠ -1 := by
    intro h
    apply hq1
    linear_combination hq3 - h
  have hj : ∀ j : ℕ, j < 4 → (q ^ j = 1 ↔ j = 0) ∧ (q ^ j = -1 ↔ j = 2) := by
    intro j hj4
    interval_cases j
    · simp [hm1]
    · simp [hq1, hqm1]
    · simp [hsq, hm1']
    · simp [hq3a, hq3b]
  have hmod : q ^ m = q ^ (m % 4) := by
    rw [← hq, pow_mod_orderOf]
  rw [hmod]
  exact hj (m % 4) (Nat.mod_lt m (by norm_num))

private theorem tch_E_two_ne_zero {p : ℕ} (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

private theorem tch_E_sub_iff {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ((2 : ℕ) ^ k - 1) % p = 0 ↔ (2 : ZMod p) ^ k = 1 := by
  have h1 : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
  have key : (((2 : ℕ) ^ k - 1 : ℕ) : ZMod p) = 0 ↔ (2 : ZMod p) ^ k = 1 := by
    rw [Nat.cast_sub h1]
    simp [sub_eq_zero]
  have hd : ((2 : ℕ) ^ k - 1) % p = 0 ↔ p ∣ (2 : ℕ) ^ k - 1 :=
    ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩
  rw [hd, ← CharP.cast_eq_zero_iff (ZMod p) p]
  exact key

private theorem tch_E_add_iff {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ((2 : ℕ) ^ k + 1) % p = 0 ↔ (2 : ZMod p) ^ k = -1 := by
  have hd : ((2 : ℕ) ^ k + 1) % p = 0 ↔ p ∣ (2 : ℕ) ^ k + 1 :=
    ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩
  rw [hd, ← CharP.cast_eq_zero_iff (ZMod p) p, eq_neg_iff_add_eq_zero]
  simp

private theorem tch_E_beq_false {p c : ℕ} (h : p ≠ c) : (p == c) = false := by
  cases hb : (p == c) with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hb) h

private theorem tch_E_sub_beq {p : ℕ} [Fact p.Prime] (hp : 2 < p) {F : ℕ}
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) (m : ℕ) :
    (((2 : ℕ) ^ (m * F) - 1) % p == 0) = (m % 4 == 0) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  rw [tch_E_sub_iff, pow_mul']
  exact (tch_E_order_four (tch_E_two_ne_zero hp) hF4 m).1

private theorem tch_E_add_beq {p : ℕ} [Fact p.Prime] (hp : 2 < p) {F : ℕ}
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) (m : ℕ) :
    (((2 : ℕ) ^ (m * F) + 1) % p == 0) = (m % 4 == 2) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  rw [tch_E_add_iff, pow_mul']
  exact (tch_E_order_four (tch_E_two_ne_zero hp) hF4 m).2

private theorem tch_E_ne_zero {p F : ℕ} (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) : F ≠ 0 := by
  rintro rfl
  rw [pow_zero, orderOf_one] at hF4
  norm_num at hF4

private theorem tch_E_scale_inj {F : ℕ} (hF : F ≠ 0) : Function.Injective (flagScaleLab F) := by
  rintro ⟨t, r, n⟩ ⟨t', r', n'⟩ h
  have ht : t = t' := congrArg TcrLab.t h
  have hr : r = r' := congrArg TcrLab.r h
  have hn : n * F = n' * F := congrArg TcrLab.n h
  have hn' : n = n' := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hF) hn
  subst ht hr hn'
  rfl

private theorem tch_E_label_scale {p : ℕ} [Fact p.Prime] (hp13 : 13 ≤ p) {F : ℕ}
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) (l : TcrLab) :
    tcrSplitT p (flagScaleLab F l) = tcrSplitFree l ∧
      tcrHalfSplitT p (flagScaleLab F l) = tcrHalfFree l := by
  obtain ⟨t, r, n⟩ := l
  have h1 := tch_E_sub_beq (show 2 < p by omega) hF4 n
  have h2 := tch_E_add_beq (show 2 < p by omega) hF4 n
  have hp3 := tch_E_beq_false (show p ≠ 3 by omega)
  have hp5 := tch_E_beq_false (show p ≠ 5 by omega)
  have hp7 := tch_E_beq_false (show p ≠ 7 by omega)
  constructor
  · simp only [tcrSplitT, tcrSplitFree, flagScaleLab, h1, h2, hp3,
      Bool.and_false, Bool.or_false]
  · simp only [tcrHalfSplitT, tcrHalfFree, tcrSplitT, tcrSplitFree, flagScaleLab, h1, h2,
      hp3, hp5, hp7, Bool.and_false, Bool.or_false]

private theorem tch_E_labelClass_scale {F : ℕ} (l : TcrLab) (hl : l.t = .A → l.r ≠ 1) :
    tcrLabelClass (flagScaleLab F l) = (tcrLabelClass l).map (flagScaleLab F) := by
  obtain ⟨t, r, n⟩ := l
  have hl' : t = .A → r ≠ 1 := hl
  show tcrLabelClass ⟨t, r, n * F⟩ = (tcrLabelClass ⟨t, r, n⟩).map (flagScaleLab F)
  simp only [tcrLabelClass, List.map_cons]
  congr 1
  cases t
  ·
    have hr1 : r ≠ 1 := hl' rfl
    simp only
    split_ifs <;> simp_all [flagScaleLab]
  · simp only
    split_ifs <;> rfl
  · simp only
    split_ifs <;> rfl
  · simp only
    split_ifs with h1 h2
    · rfl
    · simp only [flagScaleLab, mul_assoc, List.map_cons, List.map_nil]
    · rfl
  all_goals simp only [List.map_nil]

private theorem tch_E_component_A {r N n : ℕ} (k : TcrKind)
    (h : (tcrComponentLabel r N k n).t = .A) : (tcrComponentLabel r N k n).r = r := by
  cases k <;> simp only [tcrComponentLabel] at h ⊢ <;> (try split_ifs at h ⊢)
  rfl

private theorem tch_E_labsOf_scale (F : ℕ) (d : TcrCData) (hr : 2 ≤ d.r) :
    tcrLabsOf d F = (tcrLabsOf d 1).map (flagScaleLab F) := by
  unfold tcrLabsOf
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [mul_one, flagComponentLabel_scale]
  apply tch_E_labelClass_scale
  intro h
  rw [tch_E_component_A k h]
  omega

theorem flagFree_labs {p : ℕ} [Fact p.Prime] (hp13 : 13 ≤ p) {F : ℕ}
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) {d : TcrCData} (hd : 2 ≤ d.r) :
    ((tcrLabsOf d F).any (tcrSplitT p) = true → (tcrLabsOf d 1).any tcrSplitFree = true) ∧
    ((tcrLabsOf d F).any (tcrHalfSplitT p) = true → (tcrLabsOf d 1).any tcrHalfFree = true) ∧
    ∀ d2 : TcrCData, 2 ≤ d2.r →
      (tcrLabsOf d2 F).any (fun l => (tcrLabsOf d F).contains l) = true →
      (tcrLabsOf d2 1).any (fun l => (tcrLabsOf d 1).contains l) = true := by
  have hF0 : F ≠ 0 := tch_E_ne_zero hF4
  have hinj : Function.Injective (flagScaleLab F) := tch_E_scale_inj hF0
  have hdF : tcrLabsOf d F = (tcrLabsOf d 1).map (flagScaleLab F) :=
    tch_E_labsOf_scale F d hd
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨y, hy, hyp⟩ := List.any_eq_true.mp h
    rw [hdF, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
    rw [(tch_E_label_scale hp13 hF4 x).1] at hyp
    exact hyp
  · intro h
    obtain ⟨y, hy, hyp⟩ := List.any_eq_true.mp h
    rw [hdF, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
    rw [(tch_E_label_scale hp13 hF4 x).2] at hyp
    exact hyp
  · intro d2 hd2 h
    obtain ⟨y, hy, hyc⟩ := List.any_eq_true.mp h
    rw [tch_E_labsOf_scale F d2 hd2, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hyc' : (tcrLabsOf d F).contains (flagScaleLab F x) = true := hyc
    rw [hdF] at hyc'
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp (List.contains_iff_mem.mp hyc')
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact List.any_eq_true.mpr ⟨x, hx, List.contains_iff_mem.mpr ha⟩

end FlagFree

end CFSG.StandardType.TableCRes

end
