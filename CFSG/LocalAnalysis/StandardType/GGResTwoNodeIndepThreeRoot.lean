module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverPair
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6p1_hpair_chain {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p)) (a b : Fin m) :
    αv a (hv b) = (TauCeti.chainEntry a b : ZMod p) := by
  rw [hpair a b, ← TauCeti.chainEntry_eq_cartanMatrix_A]

private lemma l6p1_hpair_self {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p)) (a : Fin m) :
    αv a (hv a) = 2 := by
  rw [l6p1_hpair_chain hv αv hpair a a, TauCeti.chainEntry_self]
  simp

private lemma l6p1_refl_invol {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p))
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ l w, r l w = w - αv l w • hv l) (l : Fin m) (w : V) :
    r l (r l w) = w := by
  have hα : αv l (r l w) = -αv l w := by
    rw [hr l w, map_sub, map_smul, l6p1_hpair_self hv αv hpair l, smul_eq_mul]
    ring
  rw [hr l (r l w), hα, hr l w]
  module

private lemma l6p1_sum_beta_one {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (αv : Fin m → Module.Dual (ZMod p) V) {i : ℕ} (hi : i < m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < i + 1), αv l) =
      αv ⟨i, hi⟩ := by
  have hset : Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < i + 1) = {⟨i, hi⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hil, hlt⟩
      refine Fin.ext ?_
      show l.val = i
      omega
    · rintro rfl
      exact ⟨le_refl i, Nat.lt_succ_self i⟩
  rw [hset, Finset.sum_singleton]

private lemma l6p1_sum_coroot_one {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) {i : ℕ} (hi : i < m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < i + 1), hv l) =
      hv ⟨i, hi⟩ := by
  have hset : Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < i + 1) = {⟨i, hi⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hil, hlt⟩
      refine Fin.ext ?_
      show l.val = i
      omega
    · rintro rfl
      exact ⟨le_refl i, Nat.lt_succ_self i⟩
  rw [hset, Finset.sum_singleton]

private lemma l6p1_sum_beta_succ {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (αv : Fin m → Module.Dual (ZMod p) V) {i k : ℕ} (hik : i ≤ k) (hk : k < m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), αv l) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) +
        αv ⟨k, hk⟩ := by
  have hset : Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨hil, hlt⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
      · exact Or.inr ⟨hil, h⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨hil, hlt⟩)
      · subst h
        exact ⟨hik, Nat.lt_succ_self k⟩
      · exact ⟨hil, by omega⟩
  rw [hset, Finset.sum_insert (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _
    exact Nat.lt_irrefl k), add_comm]

private lemma l6p1_sum_coroot_succ {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) {i k : ℕ} (hik : i ≤ k) (hk : k < m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), hv l) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) +
        hv ⟨k, hk⟩ := by
  have hset : Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨hil, hlt⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
      · exact Or.inr ⟨hil, h⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨hil, hlt⟩)
      · subst h
        exact ⟨hik, Nat.lt_succ_self k⟩
      · exact ⟨hil, by omega⟩
  rw [hset, Finset.sum_insert (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _
    exact Nat.lt_irrefl k), add_comm]

private lemma l6p1_alpha_coroot_step {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p))
    {i k : ℕ} (hik : i < k) (hk : k < m) :
    αv ⟨k, hk⟩ (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) =
      -1 := by
  rw [map_sum]
  have hk1 : k - 1 < m := by omega
  have hb : (⟨k - 1, hk1⟩ : Fin m) ∈
      Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h0 : ∀ a ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k),
      a ≠ (⟨k - 1, hk1⟩ : Fin m) → αv ⟨k, hk⟩ (hv a) = 0 := by
    intro a ha ham
    have hne : a.val ≠ k - 1 := by
      intro h
      exact ham (Fin.ext h)
    have ha' : a.val < k := (Finset.mem_filter.mp ha).2.2
    rw [l6p1_hpair_chain hv αv hpair ⟨k, hk⟩ a]
    change ((TauCeti.chainEntry k a.val : ℤ) : ZMod p) = 0
    rw [TauCeti.chainEntry_eq_zero (s := k) (t := a.val) (by omega) (by omega) (by omega),
      Int.cast_zero]
  rw [Finset.sum_eq_single_of_mem (⟨k - 1, hk1⟩ : Fin m) hb h0]
  rw [l6p1_hpair_chain hv αv hpair ⟨k, hk⟩ ⟨k - 1, hk1⟩]
  have hz : TauCeti.chainEntry k (k - 1) = -1 := by
    rw [TauCeti.chainEntry_def, if_neg (by omega), if_pos (by omega)]
  rw [hz]
  norm_num

private lemma l6p1_beta_hv_step {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p))
    {i k : ℕ} (hik : i < k) (hk : k < m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) (hv ⟨k, hk⟩) =
      -1 := by
  rw [LinearMap.sum_apply]
  have hk1 : k - 1 < m := by omega
  have hb : (⟨k - 1, hk1⟩ : Fin m) ∈
      Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h0 : ∀ a ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k),
      a ≠ (⟨k - 1, hk1⟩ : Fin m) → αv a (hv ⟨k, hk⟩) = 0 := by
    intro a ha ham
    have hne : a.val ≠ k - 1 := by
      intro h
      exact ham (Fin.ext h)
    have ha' : a.val < k := (Finset.mem_filter.mp ha).2.2
    rw [l6p1_hpair_chain hv αv hpair a ⟨k, hk⟩]
    change ((TauCeti.chainEntry a.val k : ℤ) : ZMod p) = 0
    rw [TauCeti.chainEntry_eq_zero (s := a.val) (t := k) (by omega) (by omega) (by omega),
      Int.cast_zero]
  rw [Finset.sum_eq_single_of_mem (⟨k - 1, hk1⟩ : Fin m) hb h0]
  rw [l6p1_hpair_chain hv αv hpair ⟨k - 1, hk1⟩ ⟨k, hk⟩]
  have hz : TauCeti.chainEntry (k - 1) k = -1 := by
    rw [TauCeti.chainEntry_def, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [hz]
  norm_num

private lemma l6p1_conj_step {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p))
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ l w, r l w = w - αv l w • hv l)
    {i k : ℕ} (hik : i < k) (hk : k < m) (s' : V ≃ₗ[ZMod p] V)
    (hs' : ∀ w, s' w = w -
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) w •
        ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) :
    ∀ w, (r ⟨k, hk⟩ * s' * r ⟨k, hk⟩) w = w -
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), αv l) w •
        ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), hv l := by
  intro w
  have hβ : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), αv l) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) +
        αv ⟨k, hk⟩ :=
    l6p1_sum_beta_succ αv (le_of_lt hik) hk
  have hγ : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), hv l) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) +
        hv ⟨k, hk⟩ :=
    l6p1_sum_coroot_succ (p := p) hv (le_of_lt hik) hk
  have hαγ : αv ⟨k, hk⟩
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) = -1 :=
    l6p1_alpha_coroot_step hv αv hpair hik hk
  have hβh : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l)
      (hv ⟨k, hk⟩) = -1 :=
    l6p1_beta_hv_step hv αv hpair hik hk
  have hrγ : r ⟨k, hk⟩
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) + hv ⟨k, hk⟩ := by
    rw [hr ⟨k, hk⟩ (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l),
      hαγ]
    module
  have hrβ : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l)
      (r ⟨k, hk⟩ w) =
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) w +
        αv ⟨k, hk⟩ w := by
    rw [hr ⟨k, hk⟩ w, map_sub, map_smul, hβh, smul_eq_mul]
    ring
  calc (r ⟨k, hk⟩ * s' * r ⟨k, hk⟩) w
      = r ⟨k, hk⟩ (s' (r ⟨k, hk⟩ w)) := by simp only [LinearEquiv.mul_apply]
    _ = r ⟨k, hk⟩ (r ⟨k, hk⟩ w -
          (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l)
            (r ⟨k, hk⟩ w) •
            ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) := by
        rw [hs' (r ⟨k, hk⟩ w)]
    _ = r ⟨k, hk⟩ (r ⟨k, hk⟩ w) -
          (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l)
            (r ⟨k, hk⟩ w) •
            r ⟨k, hk⟩
              (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) := by
        rw [map_sub, map_smul]
    _ = w - (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l)
            (r ⟨k, hk⟩ w) •
          ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) +
            hv ⟨k, hk⟩) := by
        rw [l6p1_refl_invol hv αv hpair r hr ⟨k, hk⟩ w, hrγ]
    _ = w - ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) w +
            αv ⟨k, hk⟩ w) •
          ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) +
            hv ⟨k, hk⟩) := by
        rw [hrβ]
    _ = w - ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), αv l) +
            αv ⟨k, hk⟩) w •
          ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k), hv l) +
            hv ⟨k, hk⟩) := rfl
    _ = w - (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), αv l) w •
          (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < k + 1), hv l) := by
        rw [← hβ, ← hγ]

theorem ggChain_rootRefl_mem {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod p))
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ l w, r l w = w - αv l w • hv l) (i j : ℕ) (hij : i < j)
    (hjm : j ≤ m) :
    ∃ s ∈ Subgroup.closure (Set.range r), ∀ w, s w = w -
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l) w •
        ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), hv l := by
  revert hjm hij
  refine Nat.strong_induction_on j ?_
  intro j ih hij hjm
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with hbase | hstep
  · subst hbase
    have hi : i < m := by omega
    refine ⟨r ⟨i, hi⟩, Subgroup.subset_closure (Set.mem_range_self (f := r) ⟨i, hi⟩),
      fun w => ?_⟩
    rw [hr ⟨i, hi⟩ w, l6p1_sum_beta_one αv hi, l6p1_sum_coroot_one (p := p) hv hi]
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hi_j' : i < j' := by omega
    have hj'_m : j' < m := by omega
    obtain ⟨s', hs'mem, hs'form⟩ := ih j' (by omega) hi_j' (le_of_lt hj'_m)
    have hr_mem : r ⟨j', hj'_m⟩ ∈ Subgroup.closure (Set.range r) :=
      Subgroup.subset_closure (Set.mem_range_self (f := r) ⟨j', hj'_m⟩)
    refine ⟨r ⟨j', hj'_m⟩ * s' * r ⟨j', hj'_m⟩,
      mul_mem (mul_mem hr_mem hs'mem) hr_mem, ?_⟩
    exact l6p1_conj_step hv αv hpair r hr hi_j' hj'_m s' hs'form

end CFSG.StandardType

end
