module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.Sporadic.Co2Rank3

open MulAction
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

section Orbits

theorem mem_orbit_subgroup_iff {K : Subgroup G} {x y : X} :
    y ∈ orbit K x ↔ ∃ k ∈ K, k • x = y := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem smul_mem_orbit_subgroup {K : Subgroup G} {x y : X} {k : G} (hk : k ∈ K)
    (hy : y ∈ orbit K x) : k • y ∈ orbit K x := by
  obtain ⟨k', hk', rfl⟩ := mem_orbit_subgroup_iff.1 hy
  exact mem_orbit_subgroup_iff.2 ⟨k * k', K.mul_mem hk hk', mul_smul _ _ _⟩

theorem orbit_subgroup_mono {K K' : Subgroup G} (h : K ≤ K') (x : X) :
    orbit K x ⊆ orbit K' x := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup_iff.1 hy
  exact mem_orbit_subgroup_iff.2 ⟨k, h hk, rfl⟩

theorem orbit_subgroup_eq_singleton {K : Subgroup G} {x : X} (h : ∀ k ∈ K, k • x = x) :
    orbit K x = {x} := by
  ext y
  rw [mem_orbit_subgroup_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact h k hk
  · rintro rfl
    exact ⟨1, K.one_mem, one_smul _ _⟩

theorem disjoint_orbit_of_ncard_ne {K : Subgroup G} {x y : X}
    (h : (orbit K x).ncard ≠ (orbit K y).ncard) : Disjoint (orbit K x) (orbit K y) :=
  (orbit.eq_or_disjoint x y).resolve_left fun e => h (by rw [e])

theorem orbit_eq_of_mem {K : Subgroup G} {x y : X} (h : y ∈ orbit K x) :
    orbit K y = orbit K x :=
  orbit_eq_iff.2 h

theorem orbit_subset_or_disjoint {N : Subgroup G} {S : Set X}
    (hS : ∀ n ∈ N, ∀ y, n • y ∈ S ↔ y ∈ S) (d : X) :
    orbit N d ⊆ S ∨ Disjoint (orbit N d) S := by
  by_cases h : ∃ y ∈ orbit N d, y ∈ S
  · obtain ⟨y, hy, hyS⟩ := h
    left
    intro z hz
    rw [← orbit_eq_of_mem hy] at hz
    obtain ⟨n, hn, rfl⟩ := mem_orbit_subgroup_iff.1 hz
    exact (hS n hn y).2 hyS
  · right
    rw [Set.disjoint_left]
    exact fun y hy hyS => h ⟨y, hy, hyS⟩

theorem ncard_inter_orbit [Finite X] {N : Subgroup G} {S : Set X}
    (hS : ∀ n ∈ N, ∀ y, n • y ∈ S ↔ y ∈ S) (d : X) :
    (orbit N d ⊆ S ∧ (S ∩ orbit N d).ncard = (orbit N d).ncard) ∨
      (Disjoint (orbit N d) S ∧ (S ∩ orbit N d).ncard = 0) := by
  rcases orbit_subset_or_disjoint hS d with h | h
  · exact Or.inl ⟨h, by rw [Set.inter_eq_right.2 h]⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [Set.inter_comm, Set.disjoint_iff_inter_eq_empty.1 h, Set.ncard_empty]

theorem ncard_eq_sum_ncard_inter [Finite X] {k : ℕ} (P : Fin k → Set X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcov : ∀ x, ∃ i, x ∈ P i) (S : Set X) :
    S.ncard = ∑ i, (S ∩ P i).ncard := by
  classical
  have := Fintype.ofFinite X
  choose f hf using hcov
  rw [Set.ncard_eq_toFinset_card' S, Finset.card_eq_sum_card_fiberwise (f := f)
    (t := Finset.univ) fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.ncard_eq_toFinset_card' (S ∩ P i)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, hf x⟩
  · rintro ⟨hx, hxi⟩
    refine ⟨hx, ?_⟩
    by_contra hne
    exact Set.disjoint_left.1 (hdisj _ _ hne) (hf x) hxi

end Orbits

@[expose] def orbitalRel (H : Subgroup G) (a b x y : X) : Prop :=
  ∃ g ∈ H, g • a = x ∧ g • b = y

@[expose] def orbitalNbr (H : Subgroup G) (a b x : X) : Set X := {y | orbitalRel H a b x y}

section Orbital

variable {H : Subgroup G} {a b : X}

theorem mem_orbitalNbr {x y : X} : y ∈ orbitalNbr H a b x ↔ orbitalRel H a b x y := Iff.rfl

theorem orbitalRel_smul_iff {h : G} (hh : h ∈ H) {x y : X} :
    orbitalRel H a b (h • x) (h • y) ↔ orbitalRel H a b x y := by
  constructor
  · rintro ⟨g, hg, hx, hy⟩
    refine ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) hg, ?_, ?_⟩
    · rw [mul_smul, hx, inv_smul_smul]
    · rw [mul_smul, hy, inv_smul_smul]
  · rintro ⟨g, hg, rfl, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, mul_smul _ _ _, mul_smul _ _ _⟩

theorem orbitalNbr_smul {h : G} (hh : h ∈ H) (x : X) :
    orbitalNbr H a b (h • x) = h • orbitalNbr H a b x := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_orbitalNbr, mem_orbitalNbr,
    ← orbitalRel_smul_iff (H.inv_mem hh), inv_smul_smul]

theorem mem_orbitalNbr_self {y : X} :
    y ∈ orbitalNbr H a b a ↔ y ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b := by
  rw [mem_orbitalNbr, mem_orbit_subgroup_iff]
  constructor
  · rintro ⟨g, hg, ha, hb⟩
    exact ⟨g, ⟨hg, ha⟩, hb⟩
  · rintro ⟨g, ⟨hg, ha⟩, hb⟩
    exact ⟨g, hg, ha, hb⟩

theorem orbitalNbr_self : orbitalNbr H a b a = orbit (H ⊓ stabilizer G a : Subgroup G) b :=
  Set.ext fun _ => mem_orbitalNbr_self

theorem ncard_orbitalNbr (htr : ∀ x, ∃ g ∈ H, g • a = x) (x : X) :
    (orbitalNbr H a b x).ncard = (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard := by
  obtain ⟨g, hg, rfl⟩ := htr x
  rw [orbitalNbr_smul hg, Set.ncard_smul_set, orbitalNbr_self]

theorem not_orbitalRel_self (hab : a ≠ b) (x : X) : ¬ orbitalRel H a b x x := by
  rintro ⟨g, -, h1, h2⟩
  exact hab (MulAction.injective g (h1.trans h2.symm))

theorem orbitalRel_symm (hswap : orbitalRel H a b b a) {x y : X} (h : orbitalRel H a b x y) :
    orbitalRel H a b y x := by
  obtain ⟨g, hg, rfl, rfl⟩ := h
  obtain ⟨k, hk, hka, hkb⟩ := hswap
  exact ⟨g * k, H.mul_mem hg hk, by rw [mul_smul, hka], by rw [mul_smul, hkb]⟩

theorem card_inf_stabilizer_eq (K : Subgroup G) (x : X) :
    Nat.card (stabilizer K x) = Nat.card (K ⊓ stabilizer G x : Subgroup G) := by
  rw [← stabilizer_subgroupOf, ← Subgroup.inf_subgroupOf_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem ncard_orbit_swap [Finite G] {s : G} (hs : s ∈ H) (hsb : s • b = a) :
    (orbit (H ⊓ stabilizer G a : Subgroup G) (s • a)).ncard =
      (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard := by
  have key : ∀ x : X, (orbit (H ⊓ stabilizer G a : Subgroup G) x).ncard *
      Nat.card (stabilizer (H ⊓ stabilizer G a : Subgroup G) x) =
        Nat.card (H ⊓ stabilizer G a : Subgroup G) := fun x => by
    rw [← index_stabilizer]
    exact Subgroup.index_mul_card _
  have hconj : H ⊓ stabilizer G a ⊓ stabilizer G (s • a) =
      (H ⊓ stabilizer G a ⊓ stabilizer G b).map (MulAut.conj s).toMonoidHom := by
    have hH : H.map (MulAut.conj s).toMonoidHom = H := by
      ext g
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact H.mul_mem (H.mul_mem hs hy) (H.inv_mem hs)
      · intro hg
        refine ⟨s⁻¹ * g * s, H.mul_mem (H.mul_mem (H.inv_mem hs) hg) hs, ?_⟩
        simp [mul_assoc]
    have hinj : Function.Injective (MulAut.conj s).toMonoidHom := (MulAut.conj s).injective
    rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hH,
      ← stabilizer_smul_eq_stabilizer_map_conj, ← stabilizer_smul_eq_stabilizer_map_conj, hsb]
    exact inf_right_comm _ _ _
  have hcard : Nat.card (stabilizer (H ⊓ stabilizer G a : Subgroup G) (s • a)) =
      Nat.card (stabilizer (H ⊓ stabilizer G a : Subgroup G) b) := by
    rw [card_inf_stabilizer_eq, card_inf_stabilizer_eq, hconj,
      Subgroup.card_map_of_injective (MulAut.conj s).injective]
  have hpos : 0 < Nat.card (stabilizer (H ⊓ stabilizer G a : Subgroup G) b) := Nat.card_pos
  have h1 := key (s • a)
  have h2 := key b
  rw [hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

end Orbital

end CFSG.Sporadic.Co2Rank3
