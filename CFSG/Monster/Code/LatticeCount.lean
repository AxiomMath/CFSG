module

public import CFSG.Monster.Code.LatticeShort
public import CFSG.Monster.CodeLatticeUnimodular

public section

namespace CFSG.Monster.Code

open CFSG.Monster
open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> decide

theorem sgn_injective : Function.Injective sgn := by decide

@[expose] def fam₁Param (p : (Fin 24 × Fin 24) × (Bool × Bool)) : Fin 24 → ℤ :=
  fun k => (if k = p.1.1 then 4 * sgn p.2.1 else 0) + (if k = p.1.2 then 4 * sgn p.2.2 else 0)

@[irreducible] def fam₁Dom : Finset ((Fin 24 × Fin 24) × (Bool × Bool)) :=
  (Finset.univ.filter fun q : Fin 24 × Fin 24 => q.1 < q.2) ×ˢ Finset.univ

theorem mem_fam₁Dom {p : (Fin 24 × Fin 24) × (Bool × Bool)} : p ∈ fam₁Dom ↔ p.1.1 < p.1.2 := by
  unfold fam₁Dom
  simp

private theorem card_lt_pairs :
    (Finset.univ.filter fun q : Fin 24 × Fin 24 => q.1 < q.2).card = 276 := by
  decide +kernel

theorem card_fam₁Dom : fam₁Dom.card = 1104 := by
  unfold fam₁Dom
  rw [Finset.card_product, card_lt_pairs]
  decide +kernel

private theorem fam₁Param_ne_zero_iff {p : (Fin 24 × Fin 24) × (Bool × Bool)}
    (hp : p.1.1 < p.1.2) (k : Fin 24) : fam₁Param p k ≠ 0 ↔ k = p.1.1 ∨ k = p.1.2 := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp
  have h1 := sgn_ne_zero p.2.1
  have h2 := sgn_ne_zero p.2.2
  by_cases hk1 : k = p.1.1
  · subst hk1
    simp only [fam₁Param, ite_true, hne, ite_false, add_zero, true_or, iff_true]
    exact mul_ne_zero (by norm_num) h1
  · by_cases hk2 : k = p.1.2
    · subst hk2
      simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, or_true, iff_true]
      exact mul_ne_zero (by norm_num) h2
    · simp [fam₁Param, hk1, hk2]

theorem fam₁Param_injOn : Set.InjOn fam₁Param fam₁Dom := by
  rintro ⟨⟨i, j⟩, s, t⟩ hp ⟨⟨i', j'⟩, s', t'⟩ hq h
  have hp' : i < j := mem_fam₁Dom.1 (Finset.mem_coe.1 hp)
  have hq' : i' < j' := mem_fam₁Dom.1 (Finset.mem_coe.1 hq)
  have hsupp : ∀ k, (k = i ∨ k = j) ↔ (k = i' ∨ k = j') := fun k => by
    rw [← fam₁Param_ne_zero_iff (p := ((i, j), s, t)) hp', ← fam₁Param_ne_zero_iff
      (p := ((i', j'), s', t')) hq', h]
  have hi := (hsupp i).1 (Or.inl rfl)
  have hj := (hsupp j).1 (Or.inr rfl)
  have hi' := (hsupp i').2 (Or.inl rfl)
  have hj' := (hsupp j').2 (Or.inr rfl)
  have hij : i = i' ∧ j = j' := by
    rw [Fin.lt_def] at hp' hq'
    simp only [Fin.ext_iff] at hi hj hi' hj'
    constructor <;> ext <;> omega
  obtain ⟨rfl, rfl⟩ := hij
  have hne : i ≠ j := ne_of_lt hp'
  have hs := congrFun h i
  have ht := congrFun h j
  simp only [fam₁Param, ite_true, hne, ite_false, add_zero, Ne.symm hne, zero_add] at hs ht
  have hs' : s = s' := sgn_injective (by linarith)
  have ht' : t = t' := sgn_injective (by linarith)
  rw [hs', ht']

@[irreducible] noncomputable def fam₁Fin : Finset (Fin 24 → ℤ) := fam₁Dom.image fam₁Param

theorem card_fam₁Fin : fam₁Fin.card = 1104 := by
  unfold fam₁Fin
  rw [Finset.card_image_of_injOn fam₁Param_injOn, card_fam₁Dom]

theorem coe_fam₁Fin : (fam₁Fin : Set (Fin 24 → ℤ)) = minFamily₁ := by
  unfold fam₁Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.1.1 < p.1.2 := mem_fam₁Dom.1 (Finset.mem_coe.1 hp)
    refine ⟨?_, fun k hk => ?_⟩
    · have : (Finset.univ.filter fun k => fam₁Param p k ≠ 0) = {p.1.1, p.1.2} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        exact fam₁Param_ne_zero_iff hp' k
      rw [this, Finset.card_pair (ne_of_lt hp')]
    · have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp'
      rcases (fam₁Param_ne_zero_iff hp' k).1 hk with rfl | rfl
      · simp only [fam₁Param, ite_true, hne, ite_false, add_zero, sgn]
        split_ifs <;> norm_num
      · simp only [fam₁Param, Ne.symm hne, ite_false, ite_true, zero_add, sgn]
        split_ifs <;> norm_num
  · rintro ⟨hcard, hval⟩
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.1 hcard
    have hmem : ∀ k, u k ≠ 0 ↔ k = a ∨ k = b := fun k => by
      have := congrArg (k ∈ ·) hS
      simpa using this
    obtain ⟨i, j, hij, hsupp⟩ : ∃ i j : Fin 24, i < j ∧ ∀ k, u k ≠ 0 ↔ k = i ∨ k = j := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, hmem⟩
      · exact ⟨b, a, h, fun k => (hmem k).trans or_comm⟩
    refine ⟨((i, j), (decide (u i = -4), decide (u j = -4))), ?_, ?_⟩
    · exact Finset.mem_coe.2 (mem_fam₁Dom.2 hij)
    · funext k
      have hne : i ≠ j := ne_of_lt hij
      by_cases hk1 : k = i
      · subst hk1
        simp only [fam₁Param, ite_true, hne, ite_false, add_zero, sgn]
        rcases hval k ((hsupp k).2 (Or.inl rfl)) with h | h <;> rw [h] <;> norm_num
      · by_cases hk2 : k = j
        · subst hk2
          simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, sgn]
          rcases hval k ((hsupp k).2 (Or.inr rfl)) with h | h <;> rw [h] <;> norm_num
        · simp only [fam₁Param, hk1, hk2, ite_false, add_zero]
          by_contra h
          rcases (hsupp k).1 (Ne.symm h) with h' | h'
          · exact hk1 h'
          · exact hk2 h'

@[irreducible] noncomputable def CFin : Finset (Fin 24 → ZMod 2) := Finset.univ.filter (· ∈ C)

theorem mem_CFin {d : Fin 24 → ZMod 2} : d ∈ CFin ↔ d ∈ C := by
  unfold CFin
  rw [Finset.mem_filter]
  simp

theorem card_CFin : CFin.card = 4096 := by
  unfold CFin
  rw [Finset.card_eq_sum_ones, sum_C]
  simp

@[irreducible] noncomputable def fam₃Dom : Finset (Fin 24 × (Fin 24 → ZMod 2)) :=
  Finset.univ ×ˢ CFin

theorem mem_fam₃Dom {p : Fin 24 × (Fin 24 → ZMod 2)} : p ∈ fam₃Dom ↔ p.2 ∈ C := by
  unfold fam₃Dom
  rw [Finset.mem_product, mem_CFin]
  simp

theorem card_fam₃Dom : fam₃Dom.card = 98304 := by
  unfold fam₃Dom
  rw [Finset.card_product, card_CFin, Finset.card_univ, Fintype.card_fin]

private theorem neg_one_pow_val (t : ZMod 2) : ((-1 : ℤ) ^ t.val) = 1 - 2 * bitLift t := by
  rcases zmod2_cases t with rfl | rfl <;> rfl

theorem oddMin_injective :
    Function.Injective fun p : Fin 24 × (Fin 24 → ZMod 2) => oddMin p.1 p.2 := by
  rintro ⟨i, d⟩ ⟨i', d'⟩ h
  simp only at h
  have hval : ∀ j, oddMin i d j = (1 - 2 * bitLift (d j)) * (1 - 4 * if j = i then 1 else 0) :=
    fun j => by rw [oddMin, neg_one_pow_val]
  have hval' : ∀ j, oddMin i' d' j =
      (1 - 2 * bitLift (d' j)) * (1 - 4 * if j = i' then 1 else 0) :=
    fun j => by rw [oddMin, neg_one_pow_val]
  have hii : i = i' := by
    by_contra hne
    have h1 := congrFun h i
    rw [hval, hval', ite_eq_left rfl, ite_eq_right hne] at h1
    rcases bitLift_zero_or_one (d i) with ha | ha <;>
      rcases bitLift_zero_or_one (d' i) with hb | hb <;> rw [ha, hb] at h1 <;> norm_num at h1
  subst hii
  have hdd : d = d' := by
    funext j
    have h1 := congrFun h j
    rw [hval, hval'] at h1
    have hb : bitLift (d j) = bitLift (d' j) := by
      rcases bitLift_zero_or_one (d j) with ha | ha <;>
        rcases bitLift_zero_or_one (d' j) with hb | hb <;> rw [ha, hb] at h1 ⊢ <;>
        split_ifs at h1 <;> norm_num at h1
    rcases zmod2_cases (d j) with ha | ha <;> rcases zmod2_cases (d' j) with hb' | hb' <;>
      rw [ha, hb'] at hb ⊢ <;> first | rfl | exact absurd hb (by decide)
  rw [hdd]

@[irreducible] noncomputable def fam₃Fin : Finset (Fin 24 → ℤ) :=
  fam₃Dom.image fun p => oddMin p.1 p.2

theorem card_fam₃Fin : fam₃Fin.card = 98304 := by
  unfold fam₃Fin
  rw [Finset.card_image_of_injective _ oddMin_injective, card_fam₃Dom]

theorem coe_fam₃Fin : (fam₃Fin : Set (Fin 24 → ℤ)) = minFamily₃ := by
  unfold fam₃Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨⟨i, d⟩, hp, rfl⟩
    exact ⟨i, d, mem_fam₃Dom.1 (Finset.mem_coe.1 hp), rfl⟩
  · rintro ⟨i, d, hd, rfl⟩
    exact ⟨(i, d), Finset.mem_coe.2 (mem_fam₃Dom.2 hd), rfl⟩

@[expose] def suppFin (d : Fin 24 → ZMod 2) : Finset (Fin 24) := Finset.univ.filter (d · ≠ 0)

theorem mem_suppFin {d : Fin 24 → ZMod 2} {i : Fin 24} : i ∈ suppFin d ↔ d i ≠ 0 := by
  simp [suppFin]

@[expose] def fam₂Vec (d : Fin 24 → ZMod 2) (T : Finset (Fin 24)) : Fin 24 → ℤ :=
  fun i => if d i = 0 then 0 else if i ∈ T then -2 else 2

@[irreducible] noncomputable def octFin : Finset (Fin 24 → ZMod 2) :=
  CFin.filter (hammingNorm · = 8)

theorem mem_octFin {d : Fin 24 → ZMod 2} : d ∈ octFin ↔ d ∈ C ∧ hammingNorm d = 8 := by
  unfold octFin
  rw [Finset.mem_filter, mem_CFin]

theorem card_octFin : octFin.card = 759 := by
  unfold octFin CFin
  rw [card_filter_wt, wtCount_eight]

@[irreducible] noncomputable def fam₂Dom : Finset (Σ _ : Fin 24 → ZMod 2, Finset (Fin 24)) :=
  octFin.sigma fun d => (suppFin d).powerset.filter fun T => Even T.card

theorem mem_fam₂Dom {p : Σ _ : Fin 24 → ZMod 2, Finset (Fin 24)} :
    p ∈ fam₂Dom ↔ (p.1 ∈ C ∧ hammingNorm p.1 = 8) ∧ p.2 ⊆ suppFin p.1 ∧ Even p.2.card := by
  unfold fam₂Dom
  rw [Finset.mem_sigma, mem_octFin, Finset.mem_filter, Finset.mem_powerset]

theorem card_even_subsets {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card = 8) :
    (s.powerset.filter fun T => Even T.card).card = 128 := by
  have hne : s.Nonempty := Finset.card_pos.1 (by rw [hs]; norm_num)
  have h0 := Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun T => Even T.card)] at h0
  have he : ∑ T ∈ s.powerset.filter (fun T => Even T.card), (-1 : ℤ) ^ T.card =
      (s.powerset.filter fun T => Even T.card).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Finset.mem_filter.1 hT).2.neg_one_pow]; rfl
  have ho : ∑ T ∈ s.powerset.filter (fun T => ¬Even T.card), (-1 : ℤ) ^ T.card =
      -(s.powerset.filter fun T => ¬Even T.card).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hT).2).neg_one_pow]; rfl
  rw [he, ho] at h0
  have htot := Finset.card_filter_add_card_filter_not (s := s.powerset) (fun T => Even T.card)
  rw [Finset.card_powerset, hs] at htot
  have : ((s.powerset.filter fun T => Even T.card).card : ℤ) = 128 := by
    have h' : ((s.powerset.filter fun T => Even T.card).card : ℤ) +
        (s.powerset.filter fun T => ¬Even T.card).card = 256 := by exact_mod_cast htot
    linarith
  exact_mod_cast this

theorem card_fam₂Dom : fam₂Dom.card = 97152 := by
  unfold fam₂Dom
  rw [Finset.card_sigma]
  have : ∀ d ∈ octFin, ((suppFin d).powerset.filter fun T => Even T.card).card = 128 := by
    intro d hd
    apply card_even_subsets
    rw [suppFin, ← hammingNorm]
    exact (mem_octFin.1 hd).2
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_octFin, smul_eq_mul]

theorem fam₂Vec_injOn :
    Set.InjOn (fun p : Σ _ : Fin 24 → ZMod 2, Finset (Fin 24) => fam₂Vec p.1 p.2) fam₂Dom := by
  rintro ⟨d, T⟩ hp ⟨d', T'⟩ hq h
  have hp' := mem_fam₂Dom.1 (Finset.mem_coe.1 hp)
  have hq' := mem_fam₂Dom.1 (Finset.mem_coe.1 hq)
  simp only at h hp' hq'
  have hdd : d = d' := by
    funext i
    have h1 := congrFun h i
    simp only [fam₂Vec] at h1
    rcases zmod2_cases (d i) with ha | ha <;> rcases zmod2_cases (d' i) with hb | hb <;>
      rw [ha, hb] at h1 ⊢ <;> first | rfl | (simp at h1; split_ifs at h1; norm_num at h1)
  subst hdd
  have hTT : T = T' := by
    ext i
    have h1 := congrFun h i
    simp only [fam₂Vec] at h1
    have hT : i ∈ T → d i ≠ 0 := fun hi => mem_suppFin.1 (hp'.2.1 hi)
    have hT' : i ∈ T' → d i ≠ 0 := fun hi => mem_suppFin.1 (hq'.2.1 hi)
    by_cases hd : d i = 0
    · exact ⟨fun hi => absurd hd (hT hi), fun hi => absurd hd (hT' hi)⟩
    · simp only [hd, ite_false] at h1
      by_cases h2 : i ∈ T <;> by_cases h3 : i ∈ T' <;>
        simp only [h2, h3, ite_true, ite_false] at h1 <;>
        first | exact iff_of_true h2 h3 | exact iff_of_false h2 h3 | norm_num at h1
  rw [hTT]

@[irreducible] noncomputable def fam₂Fin : Finset (Fin 24 → ℤ) :=
  fam₂Dom.image fun p => fam₂Vec p.1 p.2

theorem card_fam₂Fin : fam₂Fin.card = 97152 := by
  unfold fam₂Fin
  rw [Finset.card_image_of_injOn fam₂Vec_injOn, card_fam₂Dom]

theorem coe_fam₂Fin : (fam₂Fin : Set (Fin 24 → ℤ)) = minFamily₂ := by
  unfold fam₂Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨⟨d, T⟩, hp, rfl⟩
    obtain ⟨⟨hd, hwt⟩, hTsub, hTeven⟩ := mem_fam₂Dom.1 (Finset.mem_coe.1 hp)
    refine ⟨d, hd, hwt, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [fam₂Vec, hi, ite_false]
      split_ifs <;> norm_num
    · simp [fam₂Vec, hi]
    · have : (Finset.univ.filter fun i => fam₂Vec d T i = -2) = T := by
        ext i
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro h
          by_contra hiT
          simp only [fam₂Vec, hiT, ite_false] at h
          split_ifs at h
        · intro hi
          have hdi : d i ≠ 0 := mem_suppFin.1 (hTsub hi)
          simp [fam₂Vec, hdi, hi]
      simp only at this ⊢
      rw [this]
      exact hTeven
  · rintro ⟨d, hd, hwt, hon, hoff, heven⟩
    refine ⟨⟨d, Finset.univ.filter fun i => u i = -2⟩, Finset.mem_coe.2 (mem_fam₂Dom.2
      ⟨⟨hd, hwt⟩, fun i hi => ?_, heven⟩), ?_⟩
    · rw [Finset.mem_filter] at hi
      rw [mem_suppFin]
      intro h0
      rw [hoff i h0] at hi
      norm_num at hi
    · funext i
      simp only [fam₂Vec, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h0 : d i = 0
      · simp [h0, hoff i h0]
      · simp only [h0, ite_false]
        rcases hon i h0 with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num

@[irreducible] noncomputable def minFin : Finset (Fin 24 → ℤ) := fam₁Fin ∪ fam₂Fin ∪ fam₃Fin

theorem coe_minFin : (minFin : Set (Fin 24 → ℤ)) = minVecs := by
  unfold minFin
  rw [Finset.coe_union, Finset.coe_union, coe_fam₁Fin, coe_fam₂Fin, coe_fam₃Fin, minVecs_eq]

theorem mem_minFin {u : Fin 24 → ℤ} : u ∈ minFin ↔ u ∈ minVecs := by
  rw [← Finset.mem_coe, coe_minFin]

theorem card_minFin : minFin.card = 196560 := by
  unfold minFin
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_fam₁Fin,
    card_fam₂Fin, card_fam₃Fin]
  · rw [← Finset.disjoint_coe, coe_fam₁Fin, coe_fam₂Fin]
    exact disjoint_minFamily₁₂
  · rw [← Finset.disjoint_coe, Finset.coe_union, coe_fam₁Fin, coe_fam₂Fin, coe_fam₃Fin]
    exact Disjoint.union_left disjoint_minFamily₁₃ disjoint_minFamily₂₃

theorem normSq_add_sub (u v : Fin 24 → ℤ) :
    normSq (u + v) + normSq (u - v) = 2 * normSq u + 2 * normSq v := by
  simp only [normSq, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem normSq_two_smul (w : Fin 24 → ℤ) : normSq ((2 : ℤ) • w) = 4 * normSq w := by
  simp only [normSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem normSq_eq_zero {u : Fin 24 → ℤ} (h : normSq u = 0) : u = 0 := by
  by_contra h0
  have := normSq_pos h0
  omega

theorem eq_or_eq_neg_of_sub_mem {u v : Fin 24 → ℤ} (hu : u ∈ minVecs) (hv : v ∈ minVecs)
    {w : Fin 24 → ℤ} (hw : w ∈ codeLattice C) (huv : (2 : ℤ) • w = u - v) : v = u ∨ v = -u := by
  have hu32 := (mem_minVecs_iff.1 hu).2
  have hv32 := (mem_minVecs_iff.1 hv).2
  by_cases hw0 : w = 0
  · left
    rw [hw0, smul_zero, eq_comm, sub_eq_zero] at huv
    exact huv.symm
  · right
    have h32 := normSq_ge hw hw0
    have h1 := normSq_add_sub u v
    rw [← huv, normSq_two_smul, hu32, hv32] at h1
    have h2 := normSq_nonneg (u + v)
    have h3 : normSq (u + v) = 0 := by linarith
    exact eq_neg_of_add_eq_zero_right (normSq_eq_zero h3)

theorem minVecs_ne_zero {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : u ≠ 0 := by
  intro h
  have := (mem_minVecs_iff.1 hu).2
  rw [h] at this
  simp [normSq] at this

theorem neg_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : -u ∈ minVecs := by
  obtain ⟨hL, hn⟩ := mem_minVecs_iff.1 hu
  refine mem_minVecs_iff.2 ⟨neg_mem_codeLattice allOnes_mem_C hL, ?_⟩
  rw [← hn, normSq, normSq]
  simp

theorem neg_ne_self_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : -u ≠ u := by
  intro h
  apply minVecs_ne_zero hu
  have h2 : u + u = 0 := by nth_rewrite 1 [← h]; exact neg_add_cancel u
  rw [← two_smul ℕ u] at h2
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)

@[expose] noncomputable def classOf (u : Fin 24 → ℤ) : codeLatticeModTwo C allOnes_mem_C :=
  open Classical in
  if h : u ∈ codeLattice C then Submodule.Quotient.mk (⟨u, h⟩ : codeLatticeSubgroup allOnes_mem_C)
  else 0

theorem classOf_eq_iff {u v : Fin 24 → ℤ} (hu : u ∈ minVecs) (hv : v ∈ minVecs) :
    classOf u = classOf v ↔ v = u ∨ v = -u := by
  simp only [classOf, dite_eq_left hu.1, dite_eq_left hv.1]
  rw [Submodule.Quotient.eq, mem_two_range_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact eq_or_eq_neg_of_sub_mem hu hv w.2 hw
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · refine ⟨⟨u, hu.1⟩, ?_⟩
      simp only [AddSubgroupClass.coe_sub]
      rw [two_smul, sub_neg_eq_add]

@[expose] def posFirst (u : Fin 24 → ℤ) : Prop := ∃ i, 0 < u i ∧ ∀ j, j < i → u j = 0

theorem posFirst_xor {u : Fin 24 → ℤ} (h0 : u ≠ 0) : (posFirst u ↔ ¬posFirst (-u)) := by
  classical
  constructor
  · rintro ⟨i, hi, hj⟩ ⟨i', hi', hj'⟩
    simp only [Pi.neg_apply, neg_pos] at hi'
    have hj'' : ∀ j, j < i' → u j = 0 := fun j hj => by
      have := hj' j hj
      simpa using this
    rcases lt_trichotomy i i' with h | h | h
    · have := hj'' i h; omega
    · subst h; omega
    · have := hj i' h; omega
  · intro hn
    have hex : (Finset.univ.filter fun i => u i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
    set i₀ := (Finset.univ.filter fun i => u i ≠ 0).min' hex
    have hi₀ : u i₀ ≠ 0 := (Finset.mem_filter.1 (Finset.min'_mem _ hex)).2
    have hlt : ∀ j, j < i₀ → u j = 0 := fun j hj => by
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hne⟩))
        (not_le.2 hj)
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · exact absurd ⟨i₀, by simp [hneg], fun j hj => by simp [hlt j hj]⟩ hn
    · exact ⟨i₀, hpos, hlt⟩

@[expose] def minHalf : Set (Fin 24 → ℤ) := {u | u ∈ minVecs ∧ posFirst u}

theorem minVecs_finite : minVecs.Finite := by
  rw [← coe_minFin]
  exact Finset.finite_toSet _

theorem ncard_minVecs : minVecs.ncard = 196560 := by
  rw [← coe_minFin, Set.ncard_coe_finset, card_minFin]

theorem minVecs_eq_half_union : minVecs = minHalf ∪ Neg.neg '' minHalf := by
  ext v
  constructor
  · intro hv
    by_cases hp : posFirst v
    · exact Or.inl ⟨hv, hp⟩
    · refine Or.inr ⟨-v, ⟨neg_mem_minVecs hv, ?_⟩, neg_neg v⟩
      by_contra h
      exact hp ((posFirst_xor (minVecs_ne_zero hv)).2 h)
  · rintro (⟨hv, -⟩ | ⟨u, ⟨hu, -⟩, rfl⟩)
    · exact hv
    · exact neg_mem_minVecs hu

theorem disjoint_minHalf : Disjoint minHalf (Neg.neg '' minHalf) := by
  rw [Set.disjoint_left]
  rintro v ⟨hv, hpv⟩ ⟨u, ⟨hu, hpu⟩, rfl⟩
  exact (posFirst_xor (minVecs_ne_zero hu)).1 hpu hpv

theorem ncard_minHalf : minHalf.ncard = 98280 := by
  have hfin : minHalf.Finite := minVecs_finite.subset fun u hu => hu.1
  have h := Set.ncard_union_eq disjoint_minHalf hfin (hfin.image _)
  rw [← minVecs_eq_half_union, neg_injective.injOn.ncard_image, ncard_minVecs] at h
  generalize minHalf.ncard = a at h ⊢
  omega

theorem card_classes :
    {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c}.ncard = 98280 := by
  have hS : {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c} =
      classOf '' minHalf := by
    ext c
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases hp : posFirst u
      · exact ⟨u, ⟨hu, hp⟩, rfl⟩
      · have hn := neg_mem_minVecs hu
        refine ⟨-u, ⟨hn, ?_⟩, ?_⟩
        · by_contra h
          exact hp ((posFirst_xor (minVecs_ne_zero hu)).2 h)
        · exact ((classOf_eq_iff hu hn).2 (Or.inr rfl)).symm
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, rfl⟩
  have hinj : Set.InjOn classOf minHalf := by
    rintro u ⟨hu1, hu2⟩ v ⟨hv1, hv2⟩ huv
    rcases (classOf_eq_iff hu1 hv1).1 huv with h | h
    · exact h.symm
    · subst h
      exact absurd hv2 ((posFirst_xor (minVecs_ne_zero hu1)).1 hu2)
  rw [hS, hinj.ncard_image, ncard_minHalf]

theorem mog_lattice_short_vectors :
    ((∀ u ∈ codeLattice C, u ≠ 0 →
        4 ≤ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ))) ∧
      ∃ u ∈ codeLattice C, u ≠ 0 ∧ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4) ∧
    minVecs = minFamily₁ ∪ minFamily₂ ∪ minFamily₃ ∧
    (Disjoint minFamily₁ minFamily₂ ∧ Disjoint minFamily₁ minFamily₃ ∧
      Disjoint minFamily₂ minFamily₃) ∧
    (minFamily₁.ncard = 1104 ∧ minFamily₂.ncard = 97152 ∧ minFamily₃.ncard = 98304 ∧
      minVecs.ncard = 196560) ∧
    (∀ c : codeLatticeModTwo C allOnes_mem_C,
      {u : Fin 24 → ℤ | u ∈ minVecs ∧ classOf u = c} = ∅ ∨
        ∃ u ∈ minVecs, -u ≠ u ∧ {v : Fin 24 → ℤ | v ∈ minVecs ∧ classOf v = c} = {u, -u}) ∧
    {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c}.ncard = 98280 := by
  have hmin : ∀ u ∈ codeLattice C, u ≠ 0 →
      4 ≤ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) := by
    intro u hu h0
    rw [codeForm_self]
    have : (32 : ℚ) ≤ normSq u := by exact_mod_cast normSq_ge hu h0
    linarith
  have hex : ∃ u ∈ codeLattice C, u ≠ 0 ∧
      codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4 := by
    have h3 : oddMin 0 0 ∈ minVecs := minFamily₃_subset ⟨0, 0, C.zero_mem, rfl⟩
    exact ⟨oddMin 0 0, h3.1, minVecs_ne_zero h3, h3.2⟩
  refine ⟨⟨hmin, hex⟩, minVecs_eq, ⟨disjoint_minFamily₁₂, disjoint_minFamily₁₃,
    disjoint_minFamily₂₃⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, card_classes⟩
  · rw [← coe_fam₁Fin, Set.ncard_coe_finset, card_fam₁Fin]
  · rw [← coe_fam₂Fin, Set.ncard_coe_finset, card_fam₂Fin]
  · rw [← coe_fam₃Fin, Set.ncard_coe_finset, card_fam₃Fin]
  · rw [← coe_minFin, Set.ncard_coe_finset, card_minFin]
  · intro c
    by_cases hc : ∃ u ∈ minVecs, classOf u = c
    · right
      obtain ⟨u, hu, rfl⟩ := hc
      refine ⟨u, hu, neg_ne_self_of_mem_minVecs hu, ?_⟩
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hv, hvc⟩
        exact (classOf_eq_iff hu hv).1 hvc.symm
      · rintro (rfl | rfl)
        · exact ⟨hu, rfl⟩
        · exact ⟨neg_mem_minVecs hu,
            ((classOf_eq_iff hu (neg_mem_minVecs hu)).2 (Or.inr rfl)).symm⟩
    · left
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hv hvc => hc ⟨v, hv, hvc⟩

end CFSG.Monster.Code
