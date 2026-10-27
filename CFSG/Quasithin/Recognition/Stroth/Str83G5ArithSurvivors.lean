module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithTransfer

import Mathlib.Tactic.LinearCombination
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithBasic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5

variable {n : ℕ}

private theorem countP_split {α : Type*} (s : Multiset α) (P Q₁ Q₂ : α → Prop)
    [DecidablePred P] [DecidablePred Q₁] [DecidablePred Q₂]
    (h : ∀ a, P a ↔ Q₁ a ∨ Q₂ a) (h' : ∀ a, ¬(Q₁ a ∧ Q₂ a)) :
    s.countP P = s.countP Q₁ + s.countP Q₂ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
    by_cases hq1 : Q₁ a
    · have hP : P a := (h a).mpr (Or.inl hq1)
      have hq2 : ¬Q₂ a := fun hq2 => h' a ⟨hq1, hq2⟩
      rw [if_pos hP, if_pos hq1, if_neg hq2]
      omega
    · by_cases hq2 : Q₂ a
      · have hP : P a := (h a).mpr (Or.inr hq2)
        rw [if_pos hP, if_neg hq1, if_pos hq2]
        omega
      · have hP : ¬P a := fun hP => ((h a).mp hP).elim hq1 hq2
        rw [if_neg hP, if_neg hq1, if_neg hq2]
        omega

private theorem countP_split_bool {α : Type*} (s : Multiset α) (P : α → Prop) (f : α → Bool)
    [DecidablePred P] :
    s.countP P = s.countP (fun a => P a ∧ f a = true) + s.countP (fun a => P a ∧ f a = false) :=
  countP_split s P _ _ (fun a => by cases f a <;> simp) (fun a => by cases f a <;> simp)

private theorem four_dvd_of_symm {α : Type*} (s : Multiset α) (P : α → Prop) [DecidablePred P]
    (f g : α → Bool)
    (h₁ : ∀ a b : Bool, s.countP (fun x => (P x ∧ f x = !a) ∧ g x = b) =
      s.countP (fun x => (P x ∧ f x = a) ∧ g x = b))
    (h₂ : ∀ a b : Bool, s.countP (fun x => (P x ∧ f x = !a) ∧ g x = !b) =
      s.countP (fun x => (P x ∧ f x = a) ∧ g x = b)) :
    4 ∣ s.countP P := by
  have e0 := countP_split_bool s P f
  have e1 := countP_split_bool s (fun x => P x ∧ f x = true) g
  have e2 := countP_split_bool s (fun x => P x ∧ f x = false) g
  have a1 := h₁ false true
  have a2 := h₁ false false
  have a3 := h₂ true true
  simp only [Bool.not_true, Bool.not_false] at a1 a2 a3
  omega

private theorem countP_singleton' {α : Type*} (p : α → Prop) [DecidablePred p] (a : α) :
    Multiset.countP p {a} = if p a then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero, zero_add]

private theorem mul_card_filter_le {α : Type*} (s : Multiset α) (f : α → ℕ) (P : α → Prop)
    [DecidablePred P] (c : ℕ) (h : ∀ a ∈ s, P a → f a = c) :
    c * (s.filter P).card ≤ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ih' := ih fun b hb hPb => h b (Multiset.mem_cons_of_mem hb) hPb
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases hPa : P a
    · rw [Multiset.filter_cons_of_pos _ hPa, Multiset.card_cons, mul_add, mul_one,
        h a (Multiset.mem_cons_self a s) hPa]
      omega
    · rw [Multiset.filter_cons_of_neg _ hPa]
      omega

private theorem four_le_card {α : Type*} {ν : Multiset α} {a b c d : α}
    (ha : a ∈ ν) (hb : b ∈ ν) (hc : c ∈ ν) (hd : d ∈ ν)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ ν.card := by
  classical
  have hnd : ({a, b, c, d} : Multiset α).Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
  have hle : ({a, b, c, d} : Multiset α) ≤ ν := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Multiset.card_le_card hle
  simpa using this

private theorem countP_eq_of_map_cls_eq (hn : n ≠ 0) {P : Coord n → Prop} [DecidablePred P]
    (hP : ∀ v w, cls v = cls w → (P v ↔ P w)) {A B : Multiset (Coord n)}
    (h : A.map cls = B.map cls) : A.countP P = B.countP P := by
  classical
  have key : ∀ C : Multiset (Coord n),
      C.countP P = (C.map cls).countP fun K => ∃ v ∈ K, P v := by
    intro C
    rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
    congr 1
    refine Multiset.filter_congr fun v _ => ?_
    constructor
    · exact fun hv => ⟨v, mem_cls_self hn v, hv⟩
    · rintro ⟨w, hw, hPw⟩
      obtain ⟨u, rfl⟩ := (mem_cls_iff hn).mp hw
      exact (hP v _ ((cls_eq_cls_iff hn).mpr ⟨u, rfl⟩)).mpr hPw
  rw [key A, key B, h]

private theorem countP_eq_of_transfer (hn : n ≠ 0) {P Q : Coord n → Prop} [DecidablePred P]
    [DecidablePred Q] (hP : ∀ v w, cls v = cls w → (P v ↔ P w)) {g : Coord n → Coord n}
    {μ : Multiset (Coord n)} (h : (μ.map g).map cls = μ.map cls) (hPQ : ∀ v, P (g v) ↔ Q v) :
    μ.countP Q = μ.countP P := by
  rw [← countP_eq_of_map_cls_eq hn hP h, Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_congr rfl fun v _ => propext (hPQ v).symm

private theorem cls_map_linear {g : Coord n → Coord n}
    (hg : ∀ (a : ZMod (2 ^ n - 1)) (v : Coord n), g (a • v) = a • g v) (v : Coord n) :
    cls (g v) = (cls v).image g := by
  classical
  simp only [cls, Finset.image_image, Function.comp_def, hg]

private theorem map_map_cls_eq {g : Coord n → Coord n}
    (hg : ∀ (a : ZMod (2 ^ n - 1)) (v : Coord n), g (a • v) = a • g v) {A B : Multiset (Coord n)}
    (h : A.map cls = B.map cls) : (A.map g).map cls = (B.map g).map cls := by
  classical
  have key : ∀ C : Multiset (Coord n), (C.map g).map cls = (C.map cls).map (Finset.image g) := by
    intro C
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => cls_map_linear hg v
  rw [key A, key B, h]

private theorem map_cls_comp {f g h : Coord n → Coord n} (hf : ∀ v, f v = h (g v))
    (hh : ∀ (a : ZMod (2 ^ n - 1)) (v : Coord n), h (a • v) = a • h v) {μ : Multiset (Coord n)}
    (hg : (μ.map g).map cls = μ.map cls) (hh' : (μ.map h).map cls = μ.map cls) :
    (μ.map f).map cls = μ.map cls := by
  have e : μ.map f = (μ.map g).map h := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => hf v
  rw [e, map_map_cls_eq hh hg, hh']

private theorem exists_mem_cls_eq {g : Coord n → Coord n} {μ : Multiset (Coord n)}
    (h : (μ.map g).map cls = μ.map cls) {φ : Coord n} (hφ : φ ∈ μ) :
    ∃ ψ ∈ μ, cls ψ = cls (g φ) := by
  have hm : cls (g φ) ∈ μ.map cls := by
    rw [← h]
    exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hφ)
  obtain ⟨ψ, hψ, e⟩ := Multiset.mem_map.mp hm
  exact ⟨ψ, hψ, e⟩

private theorem smul_neg_coord (a : ZMod (2 ^ n - 1)) (v : Coord n) : a • -v = -(a • v) := by
  ext <;> simp

private theorem smul_zero_coord (a : ZMod (2 ^ n - 1)) : a • (0 : Coord n) = 0 := by
  ext <;> simp

private theorem zero_smul_coord (v : Coord n) : (0 : ZMod (2 ^ n - 1)) • v = 0 := by
  ext <;> simp

private theorem neg_smul_coord (a : ZMod (2 ^ n - 1)) (v : Coord n) : (-a) • v = -(a • v) := by
  ext <;> simp

private theorem cls_neg_eq_neg_iff (hn : n ≠ 0) {v w : Coord n} :
    cls (-v) = cls (-w) ↔ cls v = cls w := by
  rw [cls_eq_cls_iff hn, cls_eq_cls_iff hn]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [smul_neg_coord] at hu; exact neg_inj.mp hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [smul_neg_coord]⟩

private theorem eq_zero_of_cls_zero (hn : n ≠ 0) {v : Coord n} (h : cls 0 = cls v) : v = 0 := by
  obtain ⟨u, hu⟩ := (cls_eq_cls_iff hn).mp h
  rw [smul_zero_coord] at hu
  exact hu

private theorem eq_zero_of_cls_neg (hn : Odd n) (h3 : 3 ≤ n) {v : Coord n}
    (h : cls (-v) = cls v) : v = 0 := by
  obtain ⟨u, hu⟩ := (cls_eq_cls_iff (by omega)).mp h
  have h1 := congrArg Prod.fst hu
  have h2 := congrArg Prod.snd hu
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul] at h1 h2
  refine Prod.ext ?_ ?_
  · exact eq_zero_of_two_pow_mul_eq_neg hn (by linear_combination h1)
  · exact eq_zero_of_two_pow_mul_eq_neg hn (by linear_combination h2)

private theorem card_cls_of_isUnit (hn : Odd n) (h3 : 3 ≤ n) {φ : Coord n}
    (hu : IsUnit φ.1 ∨ IsUnit φ.2) : (cls φ).card = n := by
  classical
  unfold cls
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro s hs t ht hst
  have hs' := Finset.mem_range.mp (Finset.mem_coe.mp hs)
  have ht' := Finset.mem_range.mp (Finset.mem_coe.mp ht)
  have h1 := congrArg Prod.fst hst
  have h2 := congrArg Prod.snd hst
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  refine two_pow_inj (by omega) hs' ht' ?_
  rcases hu with hu | hu
  · exact hu.mul_left_inj.mp h1
  · exact hu.mul_left_inj.mp h2

private theorem exists_sign (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ pos : ZMod (2 ^ n - 1) → Bool,
      (∀ a, pos (2 * a) = pos a) ∧ ∀ a, a ≠ 0 → pos (-a) = !pos a := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero (2 ^ n - 1) := ⟨by have := seven_le h3; omega⟩
  obtain ⟨S, hS⟩ : ∃ S : ZMod (2 ^ n - 1) → ℕ,
      ∀ a, S a = ∑ s ∈ Finset.range n, (2 ^ s * a).val := ⟨_, fun _ => rfl⟩
  have hS2 : ∀ a, S (2 * a) = S a := by
    intro a
    have e1 : ∑ i ∈ Finset.range (n + 1), (2 ^ i * a).val
        = ∑ i ∈ Finset.range n, (2 ^ (i + 1) * a).val + (2 ^ 0 * a).val :=
      Finset.sum_range_succ' (fun i => (2 ^ i * a).val) n
    have e2 : ∑ i ∈ Finset.range (n + 1), (2 ^ i * a).val
        = ∑ i ∈ Finset.range n, (2 ^ i * a).val + (2 ^ n * a).val :=
      Finset.sum_range_succ (fun i => (2 ^ i * a).val) n
    have e3 : (2 ^ n * a).val = (2 ^ 0 * a).val := by rw [two_pow_self, pow_zero]
    have e4 : ∀ s : ℕ, (2 ^ s * (2 * a)).val = (2 ^ (s + 1) * a).val := fun s =>
      congrArg ZMod.val (by ring)
    rw [hS, hS]
    simp only [e4]
    omega
  have hSneg : ∀ a, a ≠ 0 → S a + S (-a) = n * (2 ^ n - 1) := by
    intro a ha
    have hterm : ∀ s ∈ Finset.range n, (2 ^ s * a).val + (2 ^ s * -a).val = 2 ^ n - 1 := by
      intro s _
      have hne : (2 : ZMod (2 ^ n - 1)) ^ s * a ≠ 0 := fun h =>
        ha (((isUnit_two hn0).pow s).mul_right_eq_zero.mp h)
      rw [mul_neg, ZMod.neg_val, if_neg hne]
      have := ZMod.val_lt ((2 : ZMod (2 ^ n - 1)) ^ s * a)
      omega
    rw [hS, hS, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
  have hodd : Odd (n * (2 ^ n - 1)) := by
    refine hn.mul ⟨2 ^ (n - 1) - 1, ?_⟩
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  refine ⟨fun a => decide (S a < S (-a)), fun a => ?_, fun a ha => ?_⟩
  · show decide (S (2 * a) < S (-(2 * a))) = decide (S a < S (-a))
    rw [hS2, show -(2 * a) = 2 * -a by ring, hS2]
  · show decide (S (-a) < S (-(-a))) = !decide (S a < S (-a))
    rw [neg_neg]
    have h1 := hSneg a ha
    obtain ⟨k, hk⟩ := hodd
    generalize n * (2 ^ n - 1) = X at h1 hk
    by_cases hlt : S a < S (-a)
    · have : ¬S (-a) < S a := by omega
      simp [hlt, this]
    · have : S (-a) < S a := by omega
      simp [hlt, this]

private theorem four_dvd_countP (hn : Odd n) (h3 : 3 ≤ n) {m₀ : ZMod (2 ^ n - 1)}
    {μ : Multiset (Coord n)} (h₁ : (μ.map (sigma1 m₀)).map cls = μ.map cls)
    (hneg : (μ.map fun v => -v).map cls = μ.map cls) :
    4 ∣ μ.countP fun φ => φ.1 ≠ 0 ∧ φ.2 - m₀ * φ.1 ≠ 0 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨pos, hpos2, hposneg⟩ := exists_sign hn h3
  have hpospow : ∀ (u : ℕ) (a : ZMod (2 ^ n - 1)), pos (2 ^ u * a) = pos a := by
    intro u
    induction u with
    | zero => intro a; rw [pow_zero, one_mul]
    | succ u ih => intro a; rw [pow_succ', mul_assoc, hpos2, ih]
  have hunit : ∀ (u : ℕ) (a : ZMod (2 ^ n - 1)), 2 ^ u * a ≠ 0 ↔ a ≠ 0 := fun u a =>
    not_congr ((isUnit_two hn0).pow u).mul_right_eq_zero
  have key : ∀ p a : Bool, ((!p) = a) ↔ (p = !a) := by decide
  have hcls : ∀ (a b : Bool) (v w : Coord n), cls v = cls w →
      ((((v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) ∧ pos v.1 = a) ∧ pos (v.2 - m₀ * v.1) = b) ↔
        (((w.1 ≠ 0 ∧ w.2 - m₀ * w.1 ≠ 0) ∧ pos w.1 = a) ∧ pos (w.2 - m₀ * w.1) = b)) := by
    intro a b v w h
    obtain ⟨u, rfl⟩ := (cls_eq_cls_iff hn0).mp h
    have e2 : ((2 : ZMod (2 ^ n - 1)) ^ u • v).2 - m₀ * ((2 : ZMod (2 ^ n - 1)) ^ u • v).1 =
        2 ^ u * (v.2 - m₀ * v.1) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have e1 : ((2 : ZMod (2 ^ n - 1)) ^ u • v).1 = 2 ^ u * v.1 := rfl
    rw [e2, e1, hunit, hunit, hpospow, hpospow]
  have hσ : ∀ (a b : Bool) (v : Coord n),
      ((((sigma1 m₀ v).1 ≠ 0 ∧ (sigma1 m₀ v).2 - m₀ * (sigma1 m₀ v).1 ≠ 0) ∧
          pos (sigma1 m₀ v).1 = a) ∧ pos ((sigma1 m₀ v).2 - m₀ * (sigma1 m₀ v).1) = b) ↔
        (((v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) ∧ pos v.1 = !a) ∧ pos (v.2 - m₀ * v.1) = b) := by
    intro a b v
    have e1 : (sigma1 m₀ v).1 = -v.1 := rfl
    have e2 : (sigma1 m₀ v).2 - m₀ * (sigma1 m₀ v).1 = v.2 - m₀ * v.1 := by
      simp only [sigma1_fst, sigma1_snd]; ring
    rw [e2, e1]
    by_cases hx : v.1 = 0
    · simp [hx]
    · simp only [neg_ne_zero, hposneg _ hx, key]
  have hng : ∀ (a b : Bool) (v : Coord n),
      ((((-v).1 ≠ 0 ∧ (-v).2 - m₀ * (-v).1 ≠ 0) ∧ pos (-v).1 = a) ∧
          pos ((-v).2 - m₀ * (-v).1) = b) ↔
        (((v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) ∧ pos v.1 = !a) ∧ pos (v.2 - m₀ * v.1) = !b) := by
    intro a b v
    have e1 : (-v).1 = -v.1 := rfl
    have e2 : (-v).2 - m₀ * (-v).1 = -(v.2 - m₀ * v.1) := by
      simp only [Prod.fst_neg, Prod.snd_neg]; ring
    rw [e2, e1]
    by_cases hx : v.1 = 0
    · simp [hx]
    · by_cases hw : v.2 - m₀ * v.1 = 0
      · simp [hw]
      · simp only [neg_ne_zero, hposneg _ hx, hposneg _ hw, key]
  exact four_dvd_of_symm μ (fun φ => φ.1 ≠ 0 ∧ φ.2 - m₀ * φ.1 ≠ 0) (fun φ => pos φ.1)
    (fun φ => pos (φ.2 - m₀ * φ.1))
    (fun a b => countP_eq_of_transfer hn0 (hcls a b) h₁ (hσ a b))
    (fun a b => countP_eq_of_transfer hn0 (hcls a b) hneg (hng a b))

private theorem two_mul_eq_one {k₀ m₀ : ZMod (2 ^ n - 1)} (hn : n ≠ 0)
    (hT : 4 * k₀ * m₀ - 2 = 0) : 2 * k₀ * m₀ = 1 := by
  have h : 2 * (2 * k₀ * m₀ - 1) = 0 := by linear_combination hT
  have := (isUnit_two hn).mul_right_eq_zero.mp h
  linear_combination this

private theorem mPow_one_mPow_one_of_T_eq_zero {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hT : 4 * k₀ * m₀ - 2 = 0) (v : Coord n) : mPow k₀ m₀ 1 (mPow k₀ m₀ 1 v) = -v := by
  have h2 : mPow k₀ m₀ 1 (mPow k₀ m₀ 1 v) = mPow k₀ m₀ 2 v := (mPow_add k₀ m₀ 1 1 v).symm
  rw [h2, mPow_two, hT, zero_smul_coord, zero_sub]

private theorem omega_smul {m₀ a : ZMod (2 ^ n - 1)} (ha : IsUnit a) (v : Coord n) :
    ((a • v).1 ≠ 0 ∧ (a • v).2 - m₀ * (a • v).1 ≠ 0) ↔ (v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) := by
  have h1 : (a • v).1 = a * v.1 := rfl
  have h2 : (a • v).2 - m₀ * (a • v).1 = a * (v.2 - m₀ * v.1) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [h2, h1]
  simp only [ne_eq, ha.mul_right_eq_zero]

private theorem omega_mPow_one {k₀ m₀ : ZMod (2 ^ n - 1)} (hn : n ≠ 0) (hk : IsUnit k₀)
    (hm : IsUnit m₀) (e : 2 * k₀ * m₀ = 1) (v : Coord n) :
    ((mPow k₀ m₀ 1 v).1 ≠ 0 ∧ (mPow k₀ m₀ 1 v).2 - m₀ * (mPow k₀ m₀ 1 v).1 ≠ 0) ↔
      (v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) := by
  have h1 : (mPow k₀ m₀ 1 v).1 = -(2 * k₀) * (v.2 - m₀ * v.1) := by
    rw [mPow_one_fst]; linear_combination v.1 * e
  have h2 : (mPow k₀ m₀ 1 v).2 - m₀ * (mPow k₀ m₀ 1 v).1 = m₀ * v.1 := by
    rw [mPow_one_snd, mPow_one_fst]; linear_combination (v.2 - 2 * m₀ * v.1) * e
  have hu : IsUnit (-(2 * k₀)) := ((isUnit_two hn).mul hk).neg
  rw [h2, h1]
  simp only [ne_eq, hu.mul_right_eq_zero, hm.mul_right_eq_zero]
  exact and_comm

private theorem omega_mPow {k₀ m₀ : ZMod (2 ^ n - 1)} (hn : n ≠ 0) (hk : IsUnit k₀)
    (hm : IsUnit m₀) (e : 2 * k₀ * m₀ = 1) (t : ℤ) (v : Coord n) :
    ((mPow k₀ m₀ t v).1 ≠ 0 ∧ (mPow k₀ m₀ t v).2 - m₀ * (mPow k₀ m₀ t v).1 ≠ 0) ↔
      (v.1 ≠ 0 ∧ v.2 - m₀ * v.1 ≠ 0) := by
  have hinv : ∀ w : Coord n, ((mPow k₀ m₀ (-1) w).1 ≠ 0 ∧
      (mPow k₀ m₀ (-1) w).2 - m₀ * (mPow k₀ m₀ (-1) w).1 ≠ 0) ↔
        (w.1 ≠ 0 ∧ w.2 - m₀ * w.1 ≠ 0) := by
    intro w
    have h := omega_mPow_one hn hk hm e (mPow k₀ m₀ (-1) w)
    rw [mPow_mPow_neg] at h
    exact h.symm
  induction t using Int.induction_on generalizing v with
  | zero => exact Iff.rfl
  | succ k ih =>
    rw [mPow_add]
    exact (ih _).trans (omega_mPow_one hn hk hm e v)
  | pred k ih =>
    rw [show (-(k : ℤ) - 1) = -(k : ℤ) + -1 by ring, mPow_add]
    exact (ih _).trans (hinv v)

private theorem omega_val (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)} (hk : IsUnit k₀)
    (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 0) (l : Lab) :
    ((Lab.val k₀ m₀ l).1 ≠ 0 ∧ (Lab.val k₀ m₀ l).2 - m₀ * (Lab.val k₀ m₀ l).1 ≠ 0) ↔
      l.isPsi = false := by
  have hn0 : n ≠ 0 := by omega
  haveI : Nontrivial (ZMod (2 ^ n - 1)) :=
    ZMod.nontrivial_iff.mpr (by have := seven_le h3; omega)
  have e := two_mul_eq_one hn0 hT
  obtain ⟨ip, t, b, c⟩ := l
  have hsgn : IsUnit (sgn (n := n) b) := by
    cases b
    · rw [sgn_false]; exact isUnit_one
    · rw [sgn_true]; exact isUnit_one.neg
  cases ip
  · have hval : Lab.val k₀ m₀ ⟨false, t, b, c⟩ = sgn b • mPow k₀ m₀ t (chi k₀) := rfl
    have h1 : (1 : ZMod (2 ^ n - 1)) - m₀ * k₀ ≠ 0 := by
      have h2 : 2 * (1 - m₀ * k₀) = 1 := by linear_combination -e
      intro h
      rw [h, mul_zero] at h2
      exact zero_ne_one h2
    rw [hval, omega_smul hsgn, omega_mPow hn0 hk hm e]
    simp only [chi_fst, chi_snd, iff_true]
    exact ⟨hk.ne_zero, h1⟩
  · have hval : Lab.val k₀ m₀ ⟨true, t, b, c⟩ =
        sgn b • ((if c then cen n else 1) • mPow k₀ m₀ t (psi m₀)) := rfl
    have hcen : IsUnit (if c then cen n else (1 : ZMod (2 ^ n - 1))) := by
      cases c
      · exact isUnit_one
      · exact isUnit_cen hn
    rw [hval, omega_smul hsgn, omega_smul hcen, omega_mPow hn0 hk hm e]
    simp [psi]

private theorem countP_chainR_omega (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hk : IsUnit k₀) (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 0) (p : Pattern) :
    (p.chainR k₀ m₀ 0 0).countP (fun φ => φ.1 ≠ 0 ∧ φ.2 - m₀ * φ.1 ≠ 0) =
      ((p.labR 0 0).filter fun l => l.isPsi = false).card := by
  rw [Pattern.chainR_eq_map, Multiset.countP_map]
  congr 1
  exact Multiset.filter_congr fun l _ => omega_val hn h3 hk hm hT l

theorem false_of_T_eq_zero (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)} (hk : IsUnit k₀)
    (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 0) {p : Pattern}
    (hp : p = .p16 ∨ p = .p17 ∨ p = .p18 ∨ p = .p73) {μT : Multiset (Coord n)}
    (h₁ : (μT.map (sigma1 m₀)).map cls = μT.map cls)
    (h₂ : (μT.map (sigma2 k₀)).map cls = μT.map cls)
    (hb : 4 ∣ ((p.chainR k₀ m₀ 0 0 + μT).filter fun φ => φ.1 ≠ 0).card)
    (hc : 4 ∣ ((p.chainR k₀ m₀ 0 0 + μT).filter fun φ => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1).card) :
    False := by
  have hM : (μT.map (mPow k₀ m₀ 1)).map cls = μT.map cls :=
    map_cls_comp (g := sigma1 m₀) (h := sigma2 k₀) (fun v => mPow_one k₀ m₀ v)
      (sigma2_smul k₀) h₁ h₂
  have hneg : (μT.map fun v => -v).map cls = μT.map cls :=
    map_cls_comp (g := mPow k₀ m₀ 1) (h := mPow k₀ m₀ 1)
      (fun v => (mPow_one_mPow_one_of_T_eq_zero hT v).symm) (mPow_smul k₀ m₀ 1) hM hM
  have h31 := four_dvd_countP hn h3 h₁ hneg
  rw [← Multiset.countP_eq_card_filter] at hb hc
  have hsplit := countP_split (p.chainR k₀ m₀ 0 0 + μT) (fun φ : Coord n => φ.1 ≠ 0)
    (fun φ => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1) (fun φ => φ.1 ≠ 0 ∧ φ.2 - m₀ * φ.1 ≠ 0)
    (fun φ => by
      constructor
      · intro hx
        by_cases hz : φ.2 = m₀ * φ.1
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inr ⟨hx, fun h => hz (sub_eq_zero.mp h)⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx)
    (fun φ => by
      rintro ⟨⟨_, hz⟩, _, hw⟩
      exact hw (sub_eq_zero.mpr hz))
  have h4 : 4 ∣ (p.chainR k₀ m₀ 0 0 + μT).countP
      (fun φ => φ.1 ≠ 0 ∧ φ.2 - m₀ * φ.1 ≠ 0) := by
    rw [hsplit] at hb
    exact (Nat.dvd_add_right hc).mp hb
  rw [Multiset.countP_add] at h4
  have h5 := (Nat.dvd_add_left h31).mp h4
  rw [countP_chainR_omega hn h3 hk hm hT] at h5
  rcases hp with rfl | rfl | rfl | rfl <;> exact absurd h5 (by decide)

private theorem mPow_one_mPow_two_of_T_eq_one {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hT : 4 * k₀ * m₀ - 2 = 1) (v : Coord n) : mPow k₀ m₀ 1 (mPow k₀ m₀ 2 v) = -v := by
  have h2 : ∀ w, mPow k₀ m₀ 2 w = mPow k₀ m₀ 1 w - w := fun w => by
    rw [mPow_two, hT, one_smul]
  have h11 : mPow k₀ m₀ 1 (mPow k₀ m₀ 1 v) = mPow k₀ m₀ 2 v := (mPow_add k₀ m₀ 1 1 v).symm
  rw [h2 v, mPow_sub_vec, h11, h2 v]
  exact sub_sub_cancel_left _ _

private theorem isUnit_fst_or_snd (hn : Odd n) (h3 : 3 ≤ n) {k₀ : ZMod (2 ^ n - 1)}
    (hk : IsUnit k₀) {μ : Multiset (Coord n)} (h₂ : (μ.map (sigma2 k₀)).map cls = μ.map cls)
    (ha : ∀ φ ∈ μ, φ.1 = 0 ∨ IsUnit φ.1) {φ : Coord n} (hφ : φ ∈ μ) (hφ0 : φ ≠ 0) :
    IsUnit φ.1 ∨ IsUnit φ.2 := by
  by_cases h1 : φ.1 = 0
  · right
    have h2 : φ.2 ≠ 0 := fun h2 => hφ0 (Prod.ext h1 h2)
    obtain ⟨ψ, hψ, hcls⟩ := exists_mem_cls_eq h₂ hφ
    obtain ⟨u, hu⟩ := (cls_eq_cls_iff (by omega)).mp hcls
    have hfst := congrArg Prod.fst hu
    simp only [sigma2_fst, Prod.smul_fst, smul_eq_mul, h1, zero_sub] at hfst
    have two : IsUnit (2 : ZMod (2 ^ n - 1)) := isUnit_two (by omega)
    rcases ha ψ hψ with h0 | hunit
    · exfalso
      rw [h0, mul_zero, neg_eq_zero] at hfst
      exact h2 ((two.mul hk).mul_right_eq_zero.mp hfst)
    · have h4 : IsUnit (-(2 * k₀ * φ.2)) := by rw [hfst]; exact (two.pow u).mul hunit
      have h5 := h4.neg
      rw [neg_neg] at h5
      exact isUnit_of_mul_isUnit_right h5
  · exact Or.inl ((ha φ hφ).resolve_left h1)

private theorem cls_comp_or {g : Coord n → Coord n}
    (hn : Odd n) (h3 : 3 ≤ n)
    (hg : ∀ (a : ZMod (2 ^ n - 1)) (v : Coord n), g (a • v) = a • g v)
    (hgg : ∀ v, g (g v) = v) {μ : Multiset (Coord n)}
    (hgi : (μ.map g).map cls = μ.map cls) (hneg : (μ.map fun v => -v).map cls = μ.map cls)
    (hcard : (μ.filter fun v => v ≠ 0).card ≤ 3) {φ : Coord n} (hφ : φ ∈ μ) (hφ0 : φ ≠ 0) :
    cls (g φ) = cls φ ∨ cls (g φ) = cls (-φ) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hn0 : n ≠ 0 := by omega
  have hg0 : g 0 = 0 := by
    have := hg 0 0
    rwa [zero_smul_coord, zero_smul_coord] at this
  have hgφ : g φ ≠ 0 := fun h => hφ0 (by rw [← hgg φ, h, hg0])
  have hneg' : (μ.map fun v => -g v).map cls = μ.map cls :=
    map_cls_comp (f := fun v => -g v) (g := g) (h := fun v => -v) (fun v => rfl)
      (fun a v => (smul_neg_coord a v).symm) hgi hneg
  obtain ⟨b, hbμ, hb⟩ := exists_mem_cls_eq hneg hφ
  obtain ⟨c, hcμ, hc⟩ := exists_mem_cls_eq hgi hφ
  obtain ⟨d, hdμ, hd⟩ := exists_mem_cls_eq hneg' hφ
  have hb : cls b = cls (-φ) := hb
  have hd : cls d = cls (-g φ) := hd
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hφ0 (neg_eq_zero.mp (eq_zero_of_cls_zero hn0 hb))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hgφ (eq_zero_of_cls_zero hn0 hc)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hgφ (neg_eq_zero.mp (eq_zero_of_cls_zero hn0 hd))
  have hab : φ ≠ b := by
    rintro rfl
    exact hφ0 (eq_zero_of_cls_neg hn h3 hb.symm)
  have hac : φ ≠ c := by
    rintro rfl
    exact hc1 hc.symm
  have had : φ ≠ d := by
    rintro rfl
    refine hc2 ?_
    have := (cls_neg_eq_neg_iff hn0).mpr hd
    rw [neg_neg] at this
    exact this.symm
  have hbc : b ≠ c := by
    rintro rfl
    exact hc2 (hc.symm.trans hb)
  have hbd : b ≠ d := by
    rintro rfl
    exact hc1 (((cls_neg_eq_neg_iff hn0).mp (hb.symm.trans hd)).symm)
  have hcd : c ≠ d := by
    rintro rfl
    exact hgφ (eq_zero_of_cls_neg hn h3 (hc.symm.trans hd).symm)
  have := four_le_card (ν := μ.filter fun v => v ≠ 0)
    (Multiset.mem_filter.mpr ⟨hφ, hφ0⟩) (Multiset.mem_filter.mpr ⟨hbμ, hb0⟩)
    (Multiset.mem_filter.mpr ⟨hcμ, hc0⟩) (Multiset.mem_filter.mpr ⟨hdμ, hd0⟩)
    hab hac had hbc hbd hcd
  omega

private theorem eq_pm_of_cls (hn : Odd n) (h3 : 3 ≤ n) {g : Coord n → Coord n}
    (hg : ∀ (a : ZMod (2 ^ n - 1)) (v : Coord n), g (a • v) = a • g v)
    (hgg : ∀ v, g (g v) = v) {φ : Coord n} (hu : IsUnit φ.1 ∨ IsUnit φ.2)
    (h : cls (g φ) = cls φ ∨ cls (g φ) = cls (-φ)) : g φ = φ ∨ g φ = -φ := by
  have hn0 : n ≠ 0 := by omega
  have key : ∀ (ε : ZMod (2 ^ n - 1)) (u : ℕ), ε * ε = 1 → g φ = (ε * 2 ^ u) • φ →
      (2 : ZMod (2 ^ n - 1)) ^ u = 1 := by
    intro ε u hε hφg
    have h1 : φ = ((ε * 2 ^ u) * (ε * 2 ^ u)) • φ := by
      calc φ = g (g φ) := (hgg φ).symm
        _ = g ((ε * 2 ^ u) • φ) := by rw [hφg]
        _ = (ε * 2 ^ u) • g φ := hg _ _
        _ = (ε * 2 ^ u) • (ε * 2 ^ u) • φ := by rw [hφg]
        _ = ((ε * 2 ^ u) * (ε * 2 ^ u)) • φ := smul_smul _ _ _
    have hc : (ε * 2 ^ u) * (ε * 2 ^ u) = (2 : ZMod (2 ^ n - 1)) ^ (2 * u) := by
      linear_combination (2 ^ (2 * u)) * hε
    rw [hc] at h1
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
    have h2 : (2 : ZMod (2 ^ n - 1)) ^ (2 * u) = 1 := by
      rcases hu with hu | hu
      · exact hu.mul_left_inj.mp (by rw [one_mul]; exact e1.symm)
      · exact hu.mul_left_inj.mp (by rw [one_mul]; exact e2.symm)
    have h4 : n ∣ 2 * u := (two_pow_eq_one_iff (by omega) (2 * u)).mp h2
    have h5 : n ∣ u := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hn) h4
    exact (two_pow_eq_one_iff (by omega) u).mpr h5
  rcases h with h | h
  · obtain ⟨u, hu'⟩ := (cls_eq_cls_iff hn0).mp h.symm
    have := key 1 u (one_mul 1) (by rw [one_mul]; exact hu')
    left
    rw [hu', this, one_smul]
  · obtain ⟨u, hu'⟩ := (cls_eq_cls_iff hn0).mp h.symm
    have := key (-1) u (by ring) (by rw [hu', smul_neg_coord, neg_one_mul, neg_smul_coord])
    right
    rw [hu', this, one_smul]

private theorem eq_zero_of_pm {k₀ m₀ : ZMod (2 ^ n - 1)} (hn : n ≠ 0) (hk : IsUnit k₀)
    (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 1) {φ : Coord n}
    (h₁ : sigma1 m₀ φ = φ ∨ sigma1 m₀ φ = -φ) (h₂ : sigma2 k₀ φ = φ ∨ sigma2 k₀ φ = -φ) :
    φ = 0 := by
  have two : IsUnit (2 : ZMod (2 ^ n - 1)) := isUnit_two hn
  have e1 : φ.1 = 0 ∨ φ.2 = m₀ * φ.1 := by
    rcases h₁ with h | h
    · left
      have h' := congrArg Prod.fst h
      simp only [sigma1_fst] at h'
      exact two.mul_right_eq_zero.mp (by linear_combination -h')
    · right
      have h' := congrArg Prod.snd h
      simp only [sigma1_snd, Prod.snd_neg] at h'
      have : φ.2 - m₀ * φ.1 = 0 := two.mul_right_eq_zero.mp (by linear_combination h')
      linear_combination this
  have e2 : φ.2 = 0 ∨ φ.1 = k₀ * φ.2 := by
    rcases h₂ with h | h
    · left
      have h' := congrArg Prod.snd h
      simp only [sigma2_snd] at h'
      exact two.mul_right_eq_zero.mp (by linear_combination -h')
    · right
      have h' := congrArg Prod.fst h
      simp only [sigma2_fst, Prod.fst_neg] at h'
      have : φ.1 - k₀ * φ.2 = 0 := two.mul_right_eq_zero.mp (by linear_combination h')
      linear_combination this
  have h14 : IsUnit (1 - m₀ * k₀) := by
    have h4 : 4 * (1 - m₀ * k₀) = 1 := by linear_combination -hT
    exact isUnit_of_mul_isUnit_right (by rw [h4]; exact isUnit_one)
  rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2
  · exact Prod.ext h1 h2
  · exact Prod.ext h1 (hk.mul_right_eq_zero.mp (by rw [← h2]; exact h1))
  · exact Prod.ext (hm.mul_right_eq_zero.mp (by rw [← h1]; exact h2)) h2
  · have hz : φ.2 = 0 := h14.mul_right_eq_zero.mp (by linear_combination h1 + m₀ * h2)
    exact Prod.ext (by show φ.1 = 0; rw [h2, hz, mul_zero]) hz

private theorem all_zero_of_T_eq_one (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hk : IsUnit k₀) (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 1) {μ : Multiset (Coord n)}
    (h₁ : (μ.map (sigma1 m₀)).map cls = μ.map cls)
    (h₂ : (μ.map (sigma2 k₀)).map cls = μ.map cls)
    (hsize : (μ.map fun φ => (cls φ).card).sum = n * 3)
    (ha : ∀ φ ∈ μ, φ.1 = 0 ∨ IsUnit φ.1) : ∀ φ ∈ μ, φ = 0 := by
  intro φ hφ
  by_contra hφ0
  have hn0 : n ≠ 0 := by omega
  have hM : (μ.map (mPow k₀ m₀ 1)).map cls = μ.map cls :=
    map_cls_comp (g := sigma1 m₀) (h := sigma2 k₀) (fun v => mPow_one k₀ m₀ v)
      (sigma2_smul k₀) h₁ h₂
  have hM2 : (μ.map (mPow k₀ m₀ 2)).map cls = μ.map cls :=
    map_cls_comp (g := mPow k₀ m₀ 1) (h := mPow k₀ m₀ 1) (fun v => mPow_add k₀ m₀ 1 1 v)
      (mPow_smul k₀ m₀ 1) hM hM
  have hneg : (μ.map fun v => -v).map cls = μ.map cls :=
    map_cls_comp (g := mPow k₀ m₀ 2) (h := mPow k₀ m₀ 1)
      (fun v => (mPow_one_mPow_two_of_T_eq_one hT v).symm) (mPow_smul k₀ m₀ 1) hM2 hM
  have hu : ∀ ψ ∈ μ, ψ ≠ 0 → IsUnit ψ.1 ∨ IsUnit ψ.2 := fun ψ hψ hψ0 =>
    isUnit_fst_or_snd hn h3 hk h₂ ha hψ hψ0
  have hcard : (μ.filter fun v => v ≠ 0).card ≤ 3 := by
    have h1 := mul_card_filter_le μ (fun φ => (cls φ).card) (fun v => v ≠ 0) n
      (fun a ha ha0 => card_cls_of_isUnit hn h3 (hu a ha ha0))
    rw [hsize] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hs₁ := cls_comp_or hn h3 (sigma1_smul m₀) (sigma1_sigma1 m₀) h₁ hneg hcard hφ hφ0
  have hs₂ := cls_comp_or hn h3 (sigma2_smul k₀) (sigma2_sigma2 k₀) h₂ hneg hcard hφ hφ0
  have hφu := hu φ hφ hφ0
  exact hφ0 (eq_zero_of_pm hn0 hk hm hT
    (eq_pm_of_cls hn h3 (sigma1_smul m₀) (sigma1_sigma1 m₀) hφu hs₁)
    (eq_pm_of_cls hn h3 (sigma2_smul k₀) (sigma2_sigma2 k₀) hφu hs₂))

private theorem val_chi_fst (k₀ m₀ : ZMod (2 ^ n - 1)) (t : ℤ) (b c : Bool) :
    (Lab.val k₀ m₀ ⟨false, t, b, c⟩).1 = sgn b * (mPow k₀ m₀ t (chi k₀)).1 := rfl

private theorem val_psi_fst (k₀ m₀ : ZMod (2 ^ n - 1)) (t : ℤ) (b c : Bool) :
    (Lab.val k₀ m₀ ⟨true, t, b, c⟩).1 =
      sgn b * ((if c then cen n else 1) * (mPow k₀ m₀ t (psi m₀)).1) := rfl

private theorem labR_p20 : Pattern.p20.labR 0 0 =
    (⟨false, 0, false, false⟩ : Lab) ::ₘ (⟨true, 1, false, false⟩ : Lab) ::ₘ
      (⟨true, 1, false, true⟩ : Lab) ::ₘ (⟨false, 1, false, false⟩ : Lab) ::ₘ
      (⟨true, 2, false, false⟩ : Lab) ::ₘ (⟨true, 2, false, true⟩ : Lab) ::ₘ
      (⟨false, 2, false, false⟩ : Lab) ::ₘ 0 := by
  have h : (Pattern.p20.labR 0 0).map (fun l => (l.isPsi, l.t, l.neg, l.ctr)) =
      (false, 0, false, false) ::ₘ (true, 1, false, false) ::ₘ (true, 1, false, true) ::ₘ
        (false, 1, false, false) ::ₘ (true, 2, false, false) ::ₘ (true, 2, false, true) ::ₘ
        (false, 2, false, false) ::ₘ 0 := by decide
  have e : ∀ L : Multiset Lab, L = (L.map fun l => (l.isPsi, l.t, l.neg, l.ctr)).map
      fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : Lab) := fun L => by
    rw [Multiset.map_map]
    exact (Multiset.map_id' L).symm
  rw [e (Pattern.p20.labR 0 0), h]
  simp only [Multiset.map_cons, Multiset.map_zero]

private theorem card_chainR_p20 (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hk : IsUnit k₀) (hT : 4 * k₀ * m₀ - 2 = 1) :
    ((Pattern.p20.chainR k₀ m₀ 0 0).filter fun φ => φ.1 ≠ 0).card = 6 := by
  have hn0 : n ≠ 0 := by omega
  haveI : Nontrivial (ZMod (2 ^ n - 1)) :=
    ZMod.nontrivial_iff.mpr (by have := seven_le h3; omega)
  have hc : IsUnit (cen n) := isUnit_cen hn
  have hh1 : IsUnit (2 * k₀ * m₀ - 1) := by
    have h : 2 * (2 * k₀ * m₀ - 1) = 1 := by linear_combination hT
    exact isUnit_of_mul_isUnit_right (by rw [h]; exact isUnit_one)
  have hh2 : IsUnit (2 * k₀ * m₀ - 2) := by
    have h : 2 * (2 * k₀ * m₀ - 2) = -1 := by linear_combination hT
    exact isUnit_of_mul_isUnit_right (by rw [h]; exact isUnit_one.neg)
  have p1 : (mPow k₀ m₀ 1 (psi m₀)).1 = 2 * k₀ * m₀ - 1 := by
    rw [mPow_one_fst]; simp only [psi_fst, psi_snd]; ring
  have q1 : (mPow k₀ m₀ 1 (chi k₀)).1 = 0 := by
    rw [mPow_one_fst]; simp only [chi_fst, chi_snd]; linear_combination k₀ * hT
  have p2 : (mPow k₀ m₀ 2 (psi m₀)).1 = 2 * k₀ * m₀ - 2 := by
    rw [mPow_two]
    simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, p1, hT, psi_fst]; ring
  have q2 : (mPow k₀ m₀ 2 (chi k₀)).1 = -k₀ := by
    rw [mPow_two]
    simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, q1, hT, chi_fst]; ring
  have f1 : (Lab.val k₀ m₀ ⟨false, 0, false, false⟩).1 ≠ 0 := by
    rw [val_chi_fst, sgn_false, one_mul, mPow_zero, chi_fst]; exact hk.ne_zero
  have f2 : (Lab.val k₀ m₀ ⟨true, 1, false, false⟩).1 ≠ 0 := by
    rw [val_psi_fst, sgn_false, p1, if_neg Bool.false_ne_true, one_mul, one_mul]
    exact hh1.ne_zero
  have f3 : (Lab.val k₀ m₀ ⟨true, 1, false, true⟩).1 ≠ 0 := by
    rw [val_psi_fst, sgn_false, p1, if_pos rfl, one_mul]
    exact (hc.mul hh1).ne_zero
  have f4 : (Lab.val k₀ m₀ ⟨false, 1, false, false⟩).1 = 0 := by
    rw [val_chi_fst, sgn_false, q1, mul_zero]
  have f5 : (Lab.val k₀ m₀ ⟨true, 2, false, false⟩).1 ≠ 0 := by
    rw [val_psi_fst, sgn_false, p2, if_neg Bool.false_ne_true, one_mul, one_mul]
    exact hh2.ne_zero
  have f6 : (Lab.val k₀ m₀ ⟨true, 2, false, true⟩).1 ≠ 0 := by
    rw [val_psi_fst, sgn_false, p2, if_pos rfl, one_mul]
    exact (hc.mul hh2).ne_zero
  have f7 : (Lab.val k₀ m₀ ⟨false, 2, false, false⟩).1 ≠ 0 := by
    rw [val_chi_fst, sgn_false, q2, one_mul]
    exact neg_ne_zero.mpr hk.ne_zero
  rw [Pattern.chainR_eq_map, labR_p20, ← Multiset.countP_eq_card_filter]
  simp [Multiset.countP_cons, countP_singleton', f1, f2, f3, f4, f5, f6, f7]

theorem false_of_T_eq_one (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)} (hk : IsUnit k₀)
    (hm : IsUnit m₀) (hT : 4 * k₀ * m₀ - 2 = 1) {μT : Multiset (Coord n)}
    (h₁ : (μT.map (sigma1 m₀)).map cls = μT.map cls)
    (h₂ : (μT.map (sigma2 k₀)).map cls = μT.map cls)
    (hsize : (μT.map fun φ => (cls φ).card).sum = n * Pattern.p20.ell)
    (ha : ∀ φ ∈ Pattern.p20.chainR k₀ m₀ 0 0 + μT, φ.1 = 0 ∨ IsUnit φ.1)
    (hb : 4 ∣ ((Pattern.p20.chainR k₀ m₀ 0 0 + μT).filter fun φ => φ.1 ≠ 0).card) : False := by
  have hell : Pattern.p20.ell = 3 := by decide
  rw [hell] at hsize
  have hzero := all_zero_of_T_eq_one hn h3 hk hm hT h₁ h₂ hsize
    (fun φ hφ => ha φ (Multiset.mem_add.mpr (Or.inr hφ)))
  have hfil : (μT.filter fun φ => φ.1 ≠ 0) = 0 :=
    Multiset.filter_eq_nil.mpr fun φ hφ => by simp [hzero φ hφ]
  rw [Multiset.filter_add, hfil, add_zero, card_chainR_p20 hn h3 hk hT] at hb
  omega

end CFSG.Quasithin.Stroth.G5

end
