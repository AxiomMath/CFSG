module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

section Algebra

variable {G : Type*} [Group G]

private theorem mul_self_eq_inv {x : G} (hx : x ^ 3 = 1) : x * x = x⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hx)

private theorem eq_one_of_eq_inv {x : G} (hx : x ^ 3 = 1) (h : x = x⁻¹) : x = 1 := by
  have h2 : x * x = x := by rw [mul_self_eq_inv hx]; exact h.symm
  exact mul_left_cancel (h2.trans (mul_one x).symm)

private theorem eq_and_eq_of_mul_eq {u v u' v' : G} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u⁻¹) (hu' : u' = u ∨ u' = u⁻¹)
    (hv' : v' = v ∨ v' = v⁻¹) (h : u * v = u' * v') : u' = u ∧ v' = v := by
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact absurd (eq_one_of_eq_inv hv (mul_left_cancel h)) hv1
  · exact absurd (eq_one_of_eq_inv hu (mul_right_cancel h)) hu1
  · exfalso
    apply hvu
    have h2 : u * v = u * (u * (v * v)) := by
      rw [← mul_assoc, mul_self_eq_inv hu, mul_self_eq_inv hv]
      exact h
    have h3 : v = u * (v * v) := mul_left_cancel h2
    have h4 : 1 * v = u * v * v := by rw [one_mul, mul_assoc]; exact h3
    exact eq_inv_of_mul_eq_one_right (mul_right_cancel h4).symm

private theorem exists_pow_mul_of_mem_closure_insert {a : G} {s : Set G} (ha : a ^ 3 = 1)
    (hs : ∀ b ∈ s, a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure (insert a s)) :
    ∃ i : ℕ, ∃ k ∈ Subgroup.closure s, x = a ^ i * k := by
  have hK : ∀ k ∈ Subgroup.closure s, Commute a k := fun k hk =>
    Subgroup.closure_induction (p := fun k _ => Commute a k) (fun x hx => hs x hx)
      (Commute.one_right a) (fun _ _ _ _ hx hy => hx.mul_right hy)
      (fun _ _ hx => hx.inv_right) hk
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain rfl | hx := hx
    · exact ⟨1, 1, one_mem _, by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure hx, by simp⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, k, hk, rfl⟩ := hx
    obtain ⟨j, l, hl, rfl⟩ := hy
    refine ⟨i + j, k * l, mul_mem hk hl, ?_⟩
    calc a ^ i * k * (a ^ j * l) = a ^ i * (k * a ^ j) * l := by simp only [mul_assoc]
      _ = a ^ i * (a ^ j * k) * l := by rw [((hK k hk).pow_left j).eq]
      _ = a ^ (i + j) * (k * l) := by rw [pow_add]; simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨i, k, hk, rfl⟩ := hx
    refine ⟨2 * i, k⁻¹, inv_mem hk, ?_⟩
    have h2 : (a ^ i)⁻¹ = a ^ (2 * i) := by
      rw [← inv_pow, ← mul_self_eq_inv ha, ← sq, ← pow_mul]
    calc (a ^ i * k)⁻¹ = k⁻¹ * (a ^ i)⁻¹ := mul_inv_rev _ _
      _ = (a ^ i)⁻¹ * k⁻¹ := (((hK k hk).pow_left i).inv_inv.eq).symm
      _ = a ^ (2 * i) * k⁻¹ := by rw [h2]

private theorem card_closure_insert_le [Finite G] {a : G} {s : Set G} (ha : a ^ 3 = 1)
    (hs : ∀ b ∈ s, a * b = b * a) :
    Nat.card (Subgroup.closure (insert a s)) ≤ 3 * Nat.card (Subgroup.closure s) := by
  have hle : Subgroup.closure s ≤ Subgroup.closure (insert a s) :=
    Subgroup.closure_mono (Set.subset_insert a s)
  have hmem : ∀ (i : ℕ) (k : Subgroup.closure s), a ^ i * (k : G) ∈ Subgroup.closure (insert a s) :=
    fun i k => mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert a s)) i) (hle k.2)
  let f : Fin 3 × Subgroup.closure s → Subgroup.closure (insert a s) :=
    fun p => ⟨a ^ (p.1 : ℕ) * (p.2 : G), hmem _ _⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, k, hk, rfl⟩ := exists_pow_mul_of_mem_closure_insert ha hs hx
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by omega)⟩, ⟨k, hk⟩), ?_⟩
    apply Subtype.ext
    show a ^ (i % 3) * k = a ^ i * k
    rw [← pow_eq_pow_mod i ha]
  calc Nat.card (Subgroup.closure (insert a s)) ≤ Nat.card (Fin 3 × Subgroup.closure s) :=
        Nat.card_le_card_of_surjective f hf
    _ = 3 * Nat.card (Subgroup.closure s) := by simp [Nat.card_prod]

private theorem card_closure_le [Finite G] {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) (s : Finset G)
    (hs : (s : Set G) ⊆ A) : Nat.card (Subgroup.closure (s : Set G)) ≤ 3 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert] at hs ⊢
    have hsA : (s : Set G) ⊆ A := (Set.subset_insert a _).trans hs
    have haA : a ∈ A := hs (Set.mem_insert a _)
    calc Nat.card (Subgroup.closure (insert a (s : Set G)))
        ≤ 3 * Nat.card (Subgroup.closure (s : Set G)) :=
          card_closure_insert_le (hexp a haA) (fun b hb => hcomm a haA b (hsA hb))
      _ ≤ 3 * 3 ^ s.card := Nat.mul_le_mul_left 3 (ih hsA)
      _ = 3 ^ (insert a s).card := by rw [Finset.card_insert_of_notMem ha, pow_succ, mul_comm]

private theorem card_closure_pair_le [Finite G] {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) {u v : G}
    (hu : u ∈ A) (hv : v ∈ A) : Nat.card (Subgroup.closure ({u, v} : Set G)) ≤ 9 := by
  classical
  have hsub : ((({u, v} : Finset G)) : Set G) ⊆ A := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have h := card_closure_le hcomm hexp {u, v} hsub
  have h2 : ({u, v} : Finset G).card ≤ 2 := Finset.card_le_two
  have h3 : (3 : ℕ) ^ ({u, v} : Finset G).card ≤ 3 ^ 2 := Nat.pow_le_pow_right (by omega) h2
  have e : ((({u, v} : Finset G)) : Set G) = {u, v} := by simp
  rw [e] at h
  omega

private theorem card_closure_triple_le [Finite G] {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) {u v w : G}
    (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A) :
    Nat.card (Subgroup.closure ({u, v, w} : Set G)) ≤ 27 := by
  classical
  have hsub : ((({u, v, w} : Finset G)) : Set G) ⊆ A := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h := card_closure_le hcomm hexp {u, v, w} hsub
  have h2 : ({u, v, w} : Finset G).card ≤ 3 := Finset.card_le_three
  have h3 : (3 : ℕ) ^ ({u, v, w} : Finset G).card ≤ 3 ^ 3 :=
    Nat.pow_le_pow_right (by omega) h2
  have e : ((({u, v, w} : Finset G)) : Set G) = {u, v, w} := by simp
  rw [e] at h
  omega

end Algebra

section Geometry

variable {G : Type*} [Group G]

private structure IndepConfig (A : Subgroup G) (S : Set G) : Prop where
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  exp : ∀ a ∈ A, a ^ 3 = 1
  subset : S ⊆ A
  one_notMem : (1 : G) ∉ S
  three : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, v ≠ u → v ≠ u⁻¹ → w ≠ u → w ≠ u⁻¹ → w ≠ v → w ≠ v⁻¹ →
    Nat.card (Subgroup.closure ({u, v, w} : Set G)) = 27
  four : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, ∀ x ∈ S, v ≠ u → v ≠ u⁻¹ → w ≠ u → w ≠ u⁻¹ → w ≠ v →
    w ≠ v⁻¹ → x ≠ u → x ≠ u⁻¹ → x ≠ v → x ≠ v⁻¹ → x ≠ w → x ≠ w⁻¹ →
    Nat.card (Subgroup.closure ({u, v, w, x} : Set G)) = 81

private theorem eq_of_mem_closure_pair [Finite G] {A : Subgroup G} {S : Set G}
    (H : IndepConfig A S) {u v w : G} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (hvu : v ≠ u)
    (hvu' : v ≠ u⁻¹) (hmem : w ∈ Subgroup.closure ({u, v} : Set G)) :
    w = u ∨ w = u⁻¹ ∨ w = v ∨ w = v⁻¹ := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hcard := H.three u hu v hv w hw hvu hvu' h1 h2 h3 h4
  have hu' : u ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hv' : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hle : Subgroup.closure ({u, v, w} : Set G) ≤ Subgroup.closure ({u, v} : Set G) := by
    rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.2
      ⟨hu', Set.insert_subset_iff.2 ⟨hv', Set.singleton_subset_iff.2 hmem⟩⟩
  have h9 := card_closure_pair_le H.comm H.exp (H.subset hu) (H.subset hv)
  have hle' := Subgroup.card_le_of_le hle
  omega

private theorem eq_of_mem_closure_triple [Finite G] {A : Subgroup G} {S : Set G}
    (H : IndepConfig A S) {u v w x : G} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (hx : x ∈ S)
    (hvu : v ≠ u) (hvu' : v ≠ u⁻¹) (hwu : w ≠ u) (hwu' : w ≠ u⁻¹) (hwv : w ≠ v)
    (hwv' : w ≠ v⁻¹) (hmem : x ∈ Subgroup.closure ({u, v, w} : Set G)) :
    x = u ∨ x = u⁻¹ ∨ x = v ∨ x = v⁻¹ ∨ x = w ∨ x = w⁻¹ := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  have hcard := H.four u hu v hv w hw x hx hvu hvu' hwu hwu' hwv hwv' h1 h2 h3 h4 h5 h6
  have hu' : u ∈ Subgroup.closure ({u, v, w} : Set G) := Subgroup.subset_closure (by simp)
  have hv' : v ∈ Subgroup.closure ({u, v, w} : Set G) := Subgroup.subset_closure (by simp)
  have hw' : w ∈ Subgroup.closure ({u, v, w} : Set G) := Subgroup.subset_closure (by simp)
  have hle : Subgroup.closure ({u, v, w, x} : Set G) ≤ Subgroup.closure ({u, v, w} : Set G) := by
    rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.2 ⟨hu', Set.insert_subset_iff.2 ⟨hv',
      Set.insert_subset_iff.2 ⟨hw', Set.singleton_subset_iff.2 hmem⟩⟩⟩
  have h27 := card_closure_triple_le H.comm H.exp (H.subset hu) (H.subset hv) (H.subset hw)
  have hle' := Subgroup.card_le_of_le hle
  omega

private theorem mul_ne_one_and_notMem [Finite G] {A : Subgroup G} {S : Set G}
    (H : IndepConfig A S) {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hvu : v ≠ u) (hvu' : v ≠ u⁻¹) :
    u * v ≠ 1 ∧ u * v ∉ S := by
  refine ⟨fun h => hvu' (eq_inv_of_mul_eq_one_right h), fun hw => ?_⟩
  have hmem : u * v ∈ Subgroup.closure ({u, v} : Set G) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  rcases eq_of_mem_closure_pair H hu hv hw hvu hvu' hmem with h | h | h | h
  · have hv1 : v = 1 := mul_left_cancel (h.trans (mul_one u).symm)
    exact H.one_notMem (hv1 ▸ hv)
  · exact hvu (mul_left_cancel (h.trans (mul_self_eq_inv (H.exp u (H.subset hu))).symm))
  · have hu1 : u = 1 := mul_right_cancel (h.trans (one_mul v).symm)
    exact H.one_notMem (hu1 ▸ hu)
  · exact hvu (mul_right_cancel (h.trans (mul_self_eq_inv (H.exp v (H.subset hv))).symm)).symm

private theorem eq_or_swap_of_mul_eq [Finite G] {A : Subgroup G} {S : Set G}
    (H : IndepConfig A S) {u v u' v' : G} (hu : u ∈ S) (hv : v ∈ S) (hu' : u' ∈ S)
    (hv' : v' ∈ S) (hvu : v ≠ u) (hvu' : v ≠ u⁻¹) (hv'u : v' ≠ u') (hv'u' : v' ≠ u'⁻¹)
    (h : u * v = u' * v') : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  have huc : u ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hvc : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hpts : ∀ x : G, (x = u ∨ x = u⁻¹ ∨ x = v ∨ x = v⁻¹) →
      x ∈ Subgroup.closure ({u, v} : Set G) := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact huc
    · exact inv_mem huc
    · exact hvc
    · exact inv_mem hvc
  have hv'eq : v' = u'⁻¹ * (u * v) := eq_inv_mul_of_mul_eq h.symm
  have hu'eq : u' = u * v * v'⁻¹ := eq_mul_inv_of_mul_eq h.symm
  have step1 : u' = u ∨ u' = u⁻¹ ∨ u' = v ∨ u' = v⁻¹ := by
    by_contra hne
    push Not at hne
    obtain ⟨n1, n2, n3, n4⟩ := hne
    have hv'mem : v' ∈ Subgroup.closure ({u, v, u'} : Set G) := by
      rw [hv'eq]
      exact mul_mem (inv_mem (Subgroup.subset_closure (by simp)))
        (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    have hv'pt : v' = u ∨ v' = u⁻¹ ∨ v' = v ∨ v' = v⁻¹ := by
      rcases eq_of_mem_closure_triple H hu hv hu' hv' hvu hvu' n1 n2 n3 n4 hv'mem with
        h1 | h1 | h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
      · exact absurd h1 hv'u
      · exact absurd h1 hv'u'
    have hu'mem : u' ∈ Subgroup.closure ({u, v} : Set G) := by
      rw [hu'eq]
      exact mul_mem (mul_mem huc hvc) (inv_mem (hpts v' hv'pt))
    rcases eq_of_mem_closure_pair H hu hv hu' hvu hvu' hu'mem with h1 | h1 | h1 | h1
    exacts [n1 h1, n2 h1, n3 h1, n4 h1]
  have step2 : v' = u ∨ v' = u⁻¹ ∨ v' = v ∨ v' = v⁻¹ := by
    have hv'mem : v' ∈ Subgroup.closure ({u, v} : Set G) := by
      rw [hv'eq]
      exact mul_mem (inv_mem (hpts u' step1)) (mul_mem huc hvc)
    exact eq_of_mem_closure_pair H hu hv hv' hvu hvu' hv'mem
  have hu3 := H.exp u (H.subset hu)
  have hv3 := H.exp v (H.subset hv)
  have hu1 : u ≠ 1 := fun h1 => H.one_notMem (h1 ▸ hu)
  have hv1 : v ≠ 1 := fun h1 => H.one_notMem (h1 ▸ hv)
  have huv : u * v = v * u := H.comm u (H.subset hu) v (H.subset hv)
  have hvu'' : u ≠ v⁻¹ := fun h1 => hvu' (by rw [h1, inv_inv])
  have h' : v * u = u' * v' := huv.symm.trans h
  rcases step1 with h1 | h1 | h1 | h1
  · have hv'' : v' = v ∨ v' = v⁻¹ := by
      rcases step2 with h2 | h2 | h2 | h2
      · exact absurd (h2.trans h1.symm) hv'u
      · exact absurd (by rw [h2, h1]) hv'u'
      · exact Or.inl h2
      · exact Or.inr h2
    exact Or.inl (eq_and_eq_of_mul_eq hu3 hv3 hu1 hv1 hvu' (Or.inl h1) hv'' h)
  · have hv'' : v' = v ∨ v' = v⁻¹ := by
      rcases step2 with h2 | h2 | h2 | h2
      · exact absurd (by rw [h2, h1, inv_inv]) hv'u'
      · exact absurd (h2.trans h1.symm) hv'u
      · exact Or.inl h2
      · exact Or.inr h2
    exact Or.inl (eq_and_eq_of_mul_eq hu3 hv3 hu1 hv1 hvu' (Or.inr h1) hv'' h)
  · have hu'' : v' = u ∨ v' = u⁻¹ := by
      rcases step2 with h2 | h2 | h2 | h2
      · exact Or.inl h2
      · exact Or.inr h2
      · exact absurd (h2.trans h1.symm) hv'u
      · exact absurd (by rw [h2, h1]) hv'u'
    exact Or.inr (eq_and_eq_of_mul_eq hv3 hu3 hv1 hu1 hvu'' (Or.inl h1) hu'' h')
  · have hu'' : v' = u ∨ v' = u⁻¹ := by
      rcases step2 with h2 | h2 | h2 | h2
      · exact Or.inl h2
      · exact Or.inr h2
      · exact absurd (by rw [h2, h1, inv_inv]) hv'u'
      · exact absurd (h2.trans h1.symm) hv'u
    exact Or.inr (eq_and_eq_of_mul_eq hv3 hu3 hv1 hu1 hvu'' (Or.inr h1) hu'' h')

end Geometry

theorem exists_mul_of_not_mem_of_independent {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {S : Set G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1)
    (hcard : Nat.card A = 243) (hSA : S ⊆ A) (hS1 : (1 : G) ∉ S)
    (hSinv : ∀ u ∈ S, u⁻¹ ∈ S) (hScard : S.ncard = 22)
    (h3 : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, v ≠ u → v ≠ u⁻¹ → w ≠ u → w ≠ u⁻¹ → w ≠ v → w ≠ v⁻¹ →
      Nat.card (Subgroup.closure ({u, v, w} : Set G)) = 27)
    (h4 : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, ∀ x ∈ S, v ≠ u → v ≠ u⁻¹ → w ≠ u → w ≠ u⁻¹ → w ≠ v →
      w ≠ v⁻¹ → x ≠ u → x ≠ u⁻¹ → x ≠ v → x ≠ v⁻¹ → x ≠ w → x ≠ w⁻¹ →
      Nat.card (Subgroup.closure ({u, v, w, x} : Set G)) = 81) :
    ∀ z ∈ A, z ≠ 1 → z ∉ S → ∃ u ∈ S, ∃ v ∈ S, v ≠ u ∧ v ≠ u⁻¹ ∧ z = u * v := by
  classical
  have H : IndepConfig A S := ⟨hcomm, hexp, hSA, hS1, h3, h4⟩
  have : Fintype G := Fintype.ofFinite G
  let Sf : Finset G := S.toFinset
  let Af : Finset G := (A : Set G).toFinset
  have hmemSf : ∀ x, x ∈ Sf ↔ x ∈ S := fun x => Set.mem_toFinset
  have hmemAf : ∀ x, x ∈ Af ↔ x ∈ A := fun x => by simp [Af]
  have hSf : Sf.card = 22 := by
    rw [← hScard, Set.ncard_eq_toFinset_card' S]
  have hAf : Af.card = 243 := by
    rw [← hcard, ← Set.ncard_eq_toFinset_card' (A : Set G), ← Nat.card_coe_set_eq]
    rfl
  let P : Finset (G × G) := (Sf ×ˢ Sf).filter (fun p => p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹)
  have hmemP : ∀ p : G × G, p ∈ P ↔ (p.1 ∈ S ∧ p.2 ∈ S) ∧ (p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹) := by
    intro p
    simp [P, hmemSf]
  have hP : P.card = 440 := by
    have hpair : ∀ u ∈ Sf, (Sf.filter (fun v => v ≠ u ∧ v ≠ u⁻¹)).card = 20 := by
      intro u hu
      have huS : u ∈ S := (hmemSf u).1 hu
      have hne : u ≠ u⁻¹ := fun h => hS1 (eq_one_of_eq_inv (hexp u (hSA huS)) h ▸ huS)
      have hsub : ({u, u⁻¹} : Finset G) ⊆ Sf := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hu
        · rw [Finset.mem_singleton.1 hx]
          exact (hmemSf _).2 (hSinv u huS)
      have e : Sf.filter (fun v => v ≠ u ∧ v ≠ u⁻¹) = Sf \ {u, u⁻¹} := by
        ext v
        simp [not_or, and_comm]
      rw [e, Finset.card_sdiff_of_subset hsub, Finset.card_pair hne, hSf]
    calc P.card = ∑ p ∈ Sf ×ˢ Sf, if (p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹) then 1 else 0 :=
          Finset.card_filter _ _
      _ = ∑ u ∈ Sf, ∑ v ∈ Sf, if (v ≠ u ∧ v ≠ u⁻¹) then 1 else 0 := Finset.sum_product _ _ _
      _ = ∑ _u ∈ Sf, 20 := Finset.sum_congr rfl (fun u hu => by
          rw [← Finset.card_filter]; exact hpair u hu)
      _ = 440 := by simp [hSf]
  let f : G × G → G := fun p => p.1 * p.2
  have hfib : ∀ z ∈ P.image f, (P.filter (fun p => f p = z)).card ≤ 2 := by
    intro z hz
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hz
    have hp₀' := (hmemP p₀).1 hp₀
    have hsub : P.filter (fun p => f p = f p₀) ⊆ {p₀, (p₀.2, p₀.1)} := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpP, hpf⟩ := hp
      have hp' := (hmemP p).1 hpP
      rcases eq_or_swap_of_mul_eq H hp₀'.1.1 hp₀'.1.2 hp'.1.1 hp'.1.2 hp₀'.2.1 hp₀'.2.2
        hp'.2.1 hp'.2.2 hpf.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, h1, h2]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  let T : Finset G := Af \ insert 1 Sf
  have hone : (1 : G) ∉ Sf := fun h => hS1 ((hmemSf 1).1 h)
  have hsubAf : insert 1 Sf ⊆ Af := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact (hmemAf _).2 (one_mem A)
    · exact (hmemAf x).2 (hSA ((hmemSf x).1 hx))
  have hT : T.card = 220 := by
    rw [Finset.card_sdiff_of_subset hsubAf, Finset.card_insert_of_notMem hone, hSf, hAf]
  have himgT : P.image f ⊆ T := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    have hp' := (hmemP p).1 hp
    obtain ⟨h1, h2⟩ := mul_ne_one_and_notMem H hp'.1.1 hp'.1.2 hp'.2.1 hp'.2.2
    refine Finset.mem_sdiff.2 ⟨(hmemAf _).2 (mul_mem (hSA hp'.1.1) (hSA hp'.1.2)), ?_⟩
    intro hz
    rcases Finset.mem_insert.1 hz with h | h
    · exact h1 h
    · exact h2 ((hmemSf _).1 h)
  have hle : P.card ≤ 2 * (P.image f).card := Finset.card_le_mul_card_image P 2 hfib
  have himg : P.image f = T := Finset.eq_of_subset_of_card_le himgT (by omega)
  intro z hzA hz1 hzS
  have hzT : z ∈ T := by
    refine Finset.mem_sdiff.2 ⟨(hmemAf z).2 hzA, ?_⟩
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hz1 h
    · exact hzS ((hmemSf z).1 h)
  rw [← himg] at hzT
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.1 hzT
  have hp' := (hmemP p).1 hp
  exact ⟨p.1, hp'.1.1, p.2, hp'.1.2, hp'.2.1, hp'.2.2, hpz.symm⟩

end CFSG.Sporadic.Recognition.LyonsSims
