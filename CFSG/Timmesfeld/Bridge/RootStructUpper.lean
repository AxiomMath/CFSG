module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem closure_subtype_preimage_eq_top {N : Subgroup G} {S : Set G}
    (hgen : Subgroup.closure S = N) : Subgroup.closure (N.subtype ⁻¹' S) = ⊤ := by
  subst hgen
  exact Subgroup.closure_preimage_eq_top S

theorem mem_upperCentralSeries_succ_of_forall_mem {N : Subgroup G} {S : Set G} (hSN : S ⊆ N)
    (hgen : Subgroup.closure S = N) {k : ℕ} {x : N}
    (hx : ∀ t (ht : t ∈ S), ⁅x, (⟨t, hSN ht⟩ : N)⁆ ∈ Subgroup.upperCentralSeries N k) :
    x ∈ Subgroup.upperCentralSeries N (k + 1) := by
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  have hy : y ∈ Subgroup.closure (N.subtype ⁻¹' S) := by
    rw [closure_subtype_preimage_eq_top hgen]
    exact Subgroup.mem_top y
  have hZ : (Subgroup.upperCentralSeries N k).Normal := inferInstance
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hx y hy
  | one => simp
  | mul a b _ _ ha hb =>
    have h : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by group
    rw [h]
    exact mul_mem ha (hZ.conj_mem _ hb a)
  | inv a _ ha =>
    have h : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by group
    rw [h]
    exact hZ.conj_mem _ (inv_mem ha) a⁻¹

theorem exists_mem_upperCentralSeries_layer {N : Subgroup G} [Group.IsNilpotent N] {S : Set G}
    (hSN : S ⊆ N) (hgen : Subgroup.closure S = N)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ ∈ S) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ Group.nilpotencyClass N) :
    ∃ s ∈ S, ∃ hs : s ∈ N, (⟨s, hs⟩ : N) ∈ Subgroup.upperCentralSeries N i ∧
      (⟨s, hs⟩ : N) ∉ Subgroup.upperCentralSeries N (i - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hZ : Subgroup.upperCentralSeries N k ≠ ⊤ := fun h =>
    absurd (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp h) (by omega)
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries N).mp inferInstance
  have key : ∀ m j, n ≤ j + m → ∀ s ∈ S, s ∈ N.lowerCentralSeries j → ∀ hs : s ∈ N,
      (⟨s, hs⟩ : N) ∉ Subgroup.upperCentralSeries N k → ∃ s ∈ S, ∃ hs : s ∈ N,
        (⟨s, hs⟩ : N) ∈ Subgroup.upperCentralSeries N (k + 1) ∧
          (⟨s, hs⟩ : N) ∉ Subgroup.upperCentralSeries N k := by
    intro m
    induction m with
    | zero =>
      intro j hj s _ hsj hs hsZ
      have h1 : s = 1 := by
        have := N.lowerCentralSeries_antitone (show n ≤ j by omega) hsj
        rwa [hn, Subgroup.mem_bot] at this
      subst h1
      exact (hsZ (Subgroup.one_mem _)).elim
    | succ m ih =>
      intro j hj s hsS hsj hs hsZ
      by_cases hsi : (⟨s, hs⟩ : N) ∈ Subgroup.upperCentralSeries N (k + 1)
      · exact ⟨s, hsS, hs, hsi, hsZ⟩
      obtain ⟨t, htS, hst⟩ : ∃ t, ∃ ht : t ∈ S,
          ⁅(⟨s, hs⟩ : N), (⟨t, hSN ht⟩ : N)⁆ ∉ Subgroup.upperCentralSeries N k := by
        by_contra! h
        exact hsi (mem_upperCentralSeries_succ_of_forall_mem hSN hgen h)
      have hst1 : ⁅s, t⁆ ≠ 1 := by
        intro h1
        apply hst
        have : ⁅(⟨s, hs⟩ : N), (⟨t, hSN htS⟩ : N)⁆ = 1 := Subtype.ext h1
        rw [this]
        exact Subgroup.one_mem _
      have hstS : ⁅s, t⁆ ∈ S := (hcomm s hsS t htS).resolve_left hst1
      have hstj : ⁅s, t⁆ ∈ N.lowerCentralSeries (j + 1) := by
        rw [Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mem_commutator hsj (hSN htS)
      exact ih (j + 1) (by omega) _ hstS hstj (hSN hstS) hst
  obtain ⟨s, hsS, hsZ⟩ : ∃ s, ∃ hs : s ∈ S,
      (⟨s, hSN hs⟩ : N) ∉ Subgroup.upperCentralSeries N k := by
    by_contra! h
    apply hZ
    rw [eq_top_iff, ← closure_subtype_preimage_eq_top hgen, Subgroup.closure_le]
    intro y hy
    exact h y hy
  exact key n 0 (by omega) s hsS (hSN hsS) (hSN hsS) hsZ

theorem exists_mem_center_of_ne_bot {N : Subgroup G} [Group.IsNilpotent N] {S : Set G}
    (hSN : S ⊆ N) (hgen : Subgroup.closure S = N)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ ∈ S) (hN : N ≠ ⊥) :
    ∃ s ∈ S, ∃ hs : s ∈ N, (⟨s, hs⟩ : N) ∈ Subgroup.center N ∧ s ≠ 1 := by
  have h1 : 1 ≤ Group.nilpotencyClass N := by
    by_contra! h
    apply hN
    have htop : Subgroup.upperCentralSeries N 0 = ⊤ :=
      Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (by omega)
    rw [Subgroup.upperCentralSeries_zero] at htop
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at hx' ⊢
    exact congrArg Subtype.val hx'
  obtain ⟨s, hsS, hs, hs1, hs0⟩ := exists_mem_upperCentralSeries_layer hSN hgen hcomm le_rfl h1
  rw [Subgroup.upperCentralSeries_one] at hs1
  refine ⟨s, hsS, hs, hs1, fun h => hs0 ?_⟩
  subst h
  exact Subgroup.one_mem _

end CFSG.Timmesfeld.Bridge
