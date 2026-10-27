module

public import CFSG.Quasithin.H13.AS91Sec5Eker

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem E_fix_line_of_mem {e : G} (he : e ∈ c.E) {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) :
    e • m = m := by
  obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hm
  have hc : (h : G)⁻¹ * e * (h : G) ∈ c.E := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem h.2) e).mp he
    rwa [inv_inv] at h1
  have hstab : stabilizer G c.l0 = c.G2 := stabilizer_mk_one c.G2
  have hfix : ((h : G)⁻¹ * e * (h : G)) • c.l0 = c.l0 := by
    rw [← mem_stabilizer_iff, hstab]
    exact c.E_le_G2 hc
  have key : e * (h : G) = (h : G) * ((h : G)⁻¹ * e * (h : G)) := by group
  rw [← mul_smul, key, mul_smul, hfix]

private theorem ncard_onL_diff_line {n : G ⧸ c.G2} (hn : c.OnL c.x0 n) :
    ({a | c.OnL a n} \ {c.x0}).ncard = 4 := by
  have hx : c.x0 ∈ {a | c.OnL a n} := hn
  rw [Set.ncard_diff_singleton_of_mem hx, c.ncard_onL n]

private theorem orbit_subset_line {m n : G ⧸ c.G2} (hn : c.OnL c.x0 n) {p : G ⧸ c.G1}
    (hp : c.OnL p n) (hpx : p ≠ c.x0) :
    MulAction.orbit ↥(c.Eker m) p ⊆ {a | c.OnL a n} \ {c.x0} := by
  rintro _ ⟨⟨e, he⟩, rfl⟩
  have heE : e ∈ c.E := ((c.mem_Eker).mp he).1
  refine ⟨?_, ?_⟩
  · have h1 := (cInc_smul c.G1 c.G2 e p n).mpr hp
    rw [c.E_fix_line_of_mem heE hn] at h1
    exact h1
  · intro h
    have h' : e • p = c.x0 := h
    exact hpx (MulAction.injective e (h'.trans (c.smul_x0_of_mem (c.E_le_G1 heE)).symm))

private theorem orbit_card_mul_inf {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    {p : G ⧸ c.G1} (hp : c.OnL p n) (hpx : p ≠ c.x0) :
    (MulAction.orbit ↥(c.Eker m) p).ncard * Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 9 := by
  have hle : c.Eker m ≤ c.E := fun e he => ((c.mem_Eker).mp he).1
  have hHS : c.Eker m ⊓ stabilizer G p = c.Eker m ⊓ c.Eker n := by
    rw [← c.E_inf_stab_eq_Eker hn hp hpx, ← inf_assoc, inf_eq_left.mpr hle]
  have h1 : (MulAction.orbit ↥(c.Eker m) p).ncard = (stabilizer G p).relIndex (c.Eker m) := by
    rw [← MulAction.index_stabilizer ↥(c.Eker m) p,
      ← MulAction.stabilizer_subgroupOf (c.Eker m) p]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := stabilizer G p) (K := c.Eker m)
  rw [← h1, inf_comm (stabilizer G p) (c.Eker m), hHS, c.card_Eker hm] at h2
  exact h2

private theorem exists_pair_of_ncard_eq_two {α : Type*} {s : Set α} {p : α} (h2 : s.ncard = 2)
    (hp : p ∈ s) : ∃ q, q ≠ p ∧ s = {p, q} := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp h2
  rcases Set.mem_insert_iff.mp hp with rfl | h
  · exact ⟨y, fun h => hxy h.symm, rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨x, hxy, Set.pair_comm _ _⟩

theorem smul_of_card_inf_eq {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (hcard : Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 7) {p q : G ⧸ c.G1} (hp : c.OnL p n)
    (hpx : p ≠ c.x0) (hq : c.OnL q n) (hqx : q ≠ c.x0) : ∃ e ∈ c.Eker m, e • p = q := by
  have hk := c.orbit_card_mul_inf hm hn hp hpx
  rw [hcard] at hk
  have h4 : (MulAction.orbit ↥(c.Eker m) p).ncard = 4 := by
    norm_num at hk
    omega
  have heq : MulAction.orbit ↥(c.Eker m) p = {a | c.OnL a n} \ {c.x0} :=
    Set.eq_of_subset_of_ncard_le (c.orbit_subset_line (m := m) hn hp hpx)
      (le_of_eq (by rw [c.ncard_onL_diff_line hn, h4]))
  have hqo : q ∈ MulAction.orbit ↥(c.Eker m) p := by
    rw [heq]
    exact ⟨hq, fun h => hqx (Set.mem_singleton_iff.mp h)⟩
  obtain ⟨⟨e, he⟩, hes⟩ := MulAction.mem_orbit_iff.mp hqo
  exact ⟨e, he, hes⟩

theorem orbit_of_card_inf_eq {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (hcard : Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 8) {p : G ⧸ c.G1} (hp : c.OnL p n)
    (hpx : p ≠ c.x0) :
    ∃ q, c.OnL q n ∧ q ≠ c.x0 ∧ q ≠ p ∧ (∃ e ∈ c.Eker m, e • p = q) ∧
      ∀ e ∈ c.Eker m, e • p = p ∨ e • p = q := by
  have hk := c.orbit_card_mul_inf hm hn hp hpx
  rw [hcard] at hk
  have h2 : (MulAction.orbit ↥(c.Eker m) p).ncard = 2 := by
    norm_num at hk
    omega
  obtain ⟨q, hqp, horb⟩ := exists_pair_of_ncard_eq_two h2 (MulAction.mem_orbit_self p)
  have hqo : q ∈ MulAction.orbit ↥(c.Eker m) p := by
    rw [horb]
    exact Set.mem_insert_of_mem _ rfl
  have hqS := c.orbit_subset_line (m := m) hn hp hpx hqo
  refine ⟨q, hqS.1, fun h => hqS.2 (Set.mem_singleton_iff.mpr h), hqp, ?_, ?_⟩
  · obtain ⟨⟨e, he⟩, hes⟩ := MulAction.mem_orbit_iff.mp hqo
    exact ⟨e, he, hes⟩
  · intro e he
    have hmem : (⟨e, he⟩ : ↥(c.Eker m)) • p ∈ MulAction.orbit ↥(c.Eker m) p :=
      MulAction.mem_orbit p (⟨e, he⟩ : ↥(c.Eker m))
    rw [horb] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)

theorem not_le_of_card_inf_lt {m n : G ⧸ c.G2} (hn : c.OnL c.x0 n)
    (hcard : Nat.card ↥(c.Eker m ⊓ c.Eker n) < 2 ^ 9) : ¬ c.Eker n ≤ c.Eker m := by
  intro h
  rw [inf_eq_right.mpr h, c.card_Eker hn] at hcard
  exact lt_irrefl _ hcard

end Loc49

end CFSG.Quasithin.H13.AS91
