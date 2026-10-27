module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem relIndex_stab_eq_ncard (M : Subgroup G) (w : V) :
    (MulAction.stabilizer G w).relIndex M = (MulAction.orbit M w).ncard := by
  rw [← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf, Subgroup.relIndex]

@[expose] def layer (Γ : SimpleGraph V) (v u : V) : Set V := {y | Γ.Adj v y ∧ y ≠ u}

theorem layer_eq (v u : V) : layer Γ v u = Γ.neighborSet v \ {u} := by
  ext y
  simp [layer]

theorem layer_finite (F : FanTree Γ G) (v u : V) : (layer Γ v u).Finite := by
  rw [layer_eq]
  exact (F.ncard_neighborSet_le v).2.sdiff

theorem ncard_layer (F : FanTree Γ G) {v u : V} (hvu : Γ.Adj v u) :
    (layer Γ v u).ncard = Fan86.valence Γ v - 1 := by
  have := F.finite_neighborSet v
  rw [layer_eq, Set.ncard_sdiff_singleton_of_mem (show u ∈ Γ.neighborSet v from hvu),
    ← Nat.card_coe_set_eq]
  rfl


theorem step_bound (F : FanTree Γ G) {M : Subgroup G} {u v w : V} (hvu : Γ.Adj v u)
    (hvw : Γ.Adj v w) (huw : w ≠ u) (hu : ∀ m ∈ M, m • u = u) (hv : ∀ m ∈ M, m • v = v) :
    (MulAction.stabilizer G w).relIndex M ≤ Fan86.valence Γ v - 1 ∧
      ((MulAction.stabilizer G w).relIndex M = Fan86.valence Γ v - 1 →
        ∀ y, Γ.Adj v y → y ≠ u → ∃ m ∈ M, m • w = y) := by
  have hsub : MulAction.orbit M w ⊆ layer Γ v u := by
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    refine ⟨?_, fun h => huw ?_⟩
    · have := (F.adj_smul m v w).2 hvw
      rwa [hv m hm] at this
    · have h2 : m • w = m • u := by rw [hu m hm]; exact h
      exact MulAction.injective m h2
  have hle : (MulAction.orbit M w).ncard ≤ Fan86.valence Γ v - 1 := by
    rw [← ncard_layer F hvu]
    exact Set.ncard_le_ncard hsub (layer_finite F v u)
  rw [relIndex_stab_eq_ncard]
  refine ⟨hle, fun h y hy hyu => ?_⟩
  have h2 := Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_layer F hvu]; omega)
    (layer_finite F v u)
  have : y ∈ MulAction.orbit M w := by rw [h2]; exact ⟨hy, hyu⟩
  obtain ⟨⟨m, hm⟩, hmy⟩ := this
  exact ⟨m, hm, hmy⟩

@[expose] def chainGp (x : ℕ → V) (a : ℕ) (M : Subgroup G) : ℕ → Subgroup G
  | 0 => M
  | n + 1 => MulAction.stabilizer G (x (a + 2 + n)) ⊓ chainGp x a M n

theorem chainGp_le (x : ℕ → V) (a : ℕ) (M : Subgroup G) (n : ℕ) : chainGp x a M n ≤ M := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact inf_le_right.trans ih

theorem fix_of_mem_chainGp (x : ℕ → V) (a : ℕ) {M : Subgroup G} (hMa : ∀ m ∈ M, m • x a = x a)
    (hMb : ∀ m ∈ M, m • x (a + 1) = x (a + 1)) (n : ℕ) :
    ∀ m ∈ chainGp x a M n, ∀ i, a ≤ i → i ≤ a + 1 + n → m • x i = x i := by
  induction n with
  | zero =>
    intro m hm i h1 h2
    have hm' : m ∈ M := hm
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hMa m hm'
    · rw [show i = a + 1 by omega]; exact hMb m hm'
  | succ n ih =>
    intro m hm i h1 h2
    by_cases hi : i = a + 2 + n
    · rw [hi]; exact MulAction.mem_stabilizer_iff.1 hm.1
    · exact ih m hm.2 i h1 (by omega)

theorem relIndex_chain (x : ℕ → V) (a : ℕ) (M : Subgroup G) (n : ℕ) :
    (chainGp x a M n).relIndex M = ∏ j ∈ Finset.range n,
      (MulAction.stabilizer G (x (a + 2 + j))).relIndex (chainGp x a M j) := by
  induction n with
  | zero => simp [chainGp, Subgroup.relIndex_self]
  | succ n ih =>
    have h := Subgroup.relIndex_mul_relIndex (chainGp x a M (n + 1)) (chainGp x a M n) M
      inf_le_right (chainGp_le x a M n)
    have h2 : (chainGp x a M (n + 1)).relIndex (chainGp x a M n) =
        (MulAction.stabilizer G (x (a + 2 + n))).relIndex (chainGp x a M n) :=
      Subgroup.inf_relIndex_right _ _
    rw [← h, h2, ih, Finset.prod_range_succ, mul_comm]

theorem eq_of_mul_ge {x b y B : ℕ} (hx : x ≤ b) (hy : y ≤ B) (hb : 0 < b) (hB : 0 < B)
    (h : b * B ≤ x * y) : x = b ∧ y = B := by
  by_contra hne
  rw [not_and_or] at hne
  rcases hne with hne | hne
  · have h1 := Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hx hne) hy hB
    omega
  · have h1 := Nat.mul_lt_mul_of_le_of_lt hx (lt_of_le_of_ne hy hne) hb
    omega

theorem valence_sub_one_pos (F : FanTree Γ G) (v : V) : 0 < Fan86.valence Γ v - 1 := by
  have h := F.valence v
  have e : Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  omega

theorem chain_step (F : FanTree Γ G) (x : ℕ → V) (a n : ℕ)
    (hadj : ∀ i, a ≤ i → i ≤ a + n → Γ.Adj (x i) (x (i + 1)))
    (hnb : ∀ i, a ≤ i → i < a + n → x i ≠ x (i + 2)) {M : Subgroup G}
    (hMa : ∀ m ∈ M, m • x a = x a) (hMb : ∀ m ∈ M, m • x (a + 1) = x (a + 1)) {j : ℕ}
    (hj : j < n) :
    (MulAction.stabilizer G (x (a + 2 + j))).relIndex (chainGp x a M j) ≤
        Fan86.valence Γ (x (a + 1 + j)) - 1 ∧
      ((MulAction.stabilizer G (x (a + 2 + j))).relIndex (chainGp x a M j) =
          Fan86.valence Γ (x (a + 1 + j)) - 1 →
        ∀ y, Γ.Adj (x (a + 1 + j)) y → y ≠ x (a + j) →
          ∃ m ∈ chainGp x a M j, m • x (a + 2 + j) = y) := by
  have h1 : Γ.Adj (x (a + 1 + j)) (x (a + j)) := by
    have := (hadj (a + j) (by omega) (by omega)).symm
    rwa [show a + j + 1 = a + 1 + j by omega] at this
  have h2 : Γ.Adj (x (a + 1 + j)) (x (a + 2 + j)) := by
    have := hadj (a + 1 + j) (by omega) (by omega)
    rwa [show a + 1 + j + 1 = a + 2 + j by omega] at this
  have h3 : x (a + 2 + j) ≠ x (a + j) := by
    have := (hnb (a + j) (by omega) (by omega)).symm
    rwa [show a + j + 2 = a + 2 + j by omega] at this
  exact step_bound F h1 h2 h3
    (fun m hm => fix_of_mem_chainGp x a hMa hMb j m hm (a + j) (by omega) (by omega))
    (fun m hm => fix_of_mem_chainGp x a hMa hMb j m hm (a + 1 + j) (by omega) (by omega))

theorem chain_bound (F : FanTree Γ G) (x : ℕ → V) (a n : ℕ)
    (hadj : ∀ i, a ≤ i → i ≤ a + n → Γ.Adj (x i) (x (i + 1)))
    (hnb : ∀ i, a ≤ i → i < a + n → x i ≠ x (i + 2)) {M : Subgroup G}
    (hMa : ∀ m ∈ M, m • x a = x a) (hMb : ∀ m ∈ M, m • x (a + 1) = x (a + 1)) :
    (chainGp x a M n).relIndex M ≤
      ∏ j ∈ Finset.range n, (Fan86.valence Γ (x (a + 1 + j)) - 1) := by
  rw [relIndex_chain]
  exact Finset.prod_le_prod fun j hj =>
    (chain_step F x a n hadj hnb hMa hMb (Finset.mem_range.1 hj)).1

theorem chain_trans (F : FanTree Γ G) (x : ℕ → V) (a : ℕ) :
    ∀ (n : ℕ), (∀ i, a ≤ i → i ≤ a + n → Γ.Adj (x i) (x (i + 1))) →
    (∀ i, a ≤ i → i < a + n → x i ≠ x (i + 2)) → ∀ {M : Subgroup G},
    (∀ m ∈ M, m • x a = x a) → (∀ m ∈ M, m • x (a + 1) = x (a + 1)) →
    ∏ j ∈ Finset.range n, (Fan86.valence Γ (x (a + 1 + j)) - 1) ≤
      (chainGp x a M n).relIndex M →
    ∀ j < n, ∀ y, Γ.Adj (x (a + 1 + j)) y → y ≠ x (a + j) →
      ∃ m ∈ chainGp x a M j, m • x (a + 2 + j) = y := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ j hj; omega
  | succ n ih =>
    intro hadj hnb M hMa hMb htight j hj y hy hyu
    have hadj' : ∀ i, a ≤ i → i ≤ a + n → Γ.Adj (x i) (x (i + 1)) :=
      fun i h1 h2 => hadj i h1 (by omega)
    have hnb' : ∀ i, a ≤ i → i < a + n → x i ≠ x (i + 2) :=
      fun i h1 h2 => hnb i h1 (by omega)
    have hn := chain_bound F x a n hadj' hnb' hMa hMb
    have hstep := chain_step F x a (n + 1) hadj hnb hMa hMb (Nat.lt_succ_self n)
    have hrel : (chainGp x a M (n + 1)).relIndex M =
        (MulAction.stabilizer G (x (a + 2 + n))).relIndex (chainGp x a M n) *
          (chainGp x a M n).relIndex M := by
      rw [relIndex_chain, relIndex_chain, Finset.prod_range_succ, mul_comm]
    rw [Finset.prod_range_succ, hrel, mul_comm] at htight
    have hb := Nat.sub_pos_of_lt (show 1 < Fan86.valence Γ (x (a + 1 + n)) by
      have := valence_sub_one_pos F (x (a + 1 + n)); omega)
    have hB : 0 < ∏ j ∈ Finset.range n, (Fan86.valence Γ (x (a + 1 + j)) - 1) :=
      Finset.prod_pos fun i _ => valence_sub_one_pos F _
    obtain ⟨h1, h2⟩ := eq_of_mul_ge hstep.1 hn (valence_sub_one_pos F _) hB htight
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjn | hjn
    · exact ih hadj' hnb' hMa hMb (by rw [h2]) j hjn y hy hyu
    · subst hjn
      exact hstep.2 h1 y hy hyu

end P71

end CFSG.Quasithin.Fan86
