module

import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.GMS.Graph
public import CFSG.Monster.GMS.S31Three
public import CFSG.Monster.GMS.Facts.BabyTables

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Generic

variable {G : Type*} [Group G]

theorem isConj_conj_self (c x : G) : IsConj x (c * x * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩

theorem isConj_conj_conj {x y : G} (c : G) (h : IsConj x y) :
    IsConj (c * x * c⁻¹) (c * y * c⁻¹) := by
  obtain ⟨d, hd⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c * d * c⁻¹, by rw [← hd]; group⟩

structure IsBabyCover (b : G) (φ : Subgroup.centralizer ({b} : Set G) →* B) : Prop where
  orderOf_eq : orderOf b = 2
  surjective : Function.Surjective φ
  ker_eq : φ.ker.map (Subgroup.centralizer ({b} : Set G)).subtype = Subgroup.zpowers b

theorem IsTwoBabyCentralizer.exists_cover {b : G} (h : IsTwoBabyCentralizer b) :
    ∃ φ : Subgroup.centralizer ({b} : Set G) →* B, IsBabyCover b φ := by
  obtain ⟨hb, -, φ, hφ, hker⟩ := h
  exact ⟨φ, hb, hφ, hker⟩

noncomputable def coverMap {b : G} (φ : Subgroup.centralizer ({b} : Set G) →* B) (g : G) : B := by
  classical exact if hg : g ∈ Subgroup.centralizer ({b} : Set G) then φ ⟨g, hg⟩ else 1

theorem mem_zpowers_iff_of_orderOf_eq_two {w y : G} (hw : orderOf w = 2) :
    y ∈ Subgroup.zpowers w ↔ y = 1 ∨ y = w := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mod_orderOf, hw]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

section Basic

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

theorem coverMap_apply {g : G} (hg : g ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ g = φ ⟨g, hg⟩ := by
  simp [coverMap, hg]

theorem coverMap_mul {x y : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ (x * y) = coverMap φ x * coverMap φ y := by
  rw [coverMap_apply (Subgroup.mul_mem _ hx hy), coverMap_apply hx, coverMap_apply hy,
    ← map_mul]
  rfl

theorem coverMap_one : coverMap φ (1 : G) = 1 := by
  rw [coverMap_apply (Subgroup.one_mem _)]
  exact map_one φ

theorem coverMap_inv {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ x⁻¹ = (coverMap φ x)⁻¹ := by
  rw [coverMap_apply (Subgroup.inv_mem _ hx), coverMap_apply hx, ← map_inv]
  rfl

theorem coverMap_conj {g x : G} (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ (g * x * g⁻¹) = coverMap φ g * coverMap φ x * (coverMap φ g)⁻¹ := by
  rw [coverMap_mul (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg), coverMap_mul hg hx,
    coverMap_inv hg]

theorem coverMap_pow {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (n : ℕ) :
    coverMap φ (x ^ n) = coverMap φ x ^ n := by
  induction n with
  | zero => simp [coverMap_one]
  | succ n ih =>
    rw [pow_succ, coverMap_mul (Subgroup.pow_mem _ hx n) hx, ih, pow_succ]

theorem mem_centralizer_self (b : G) : b ∈ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

variable (h : IsBabyCover b φ)

include h

theorem IsBabyCover.mul_self_b : b * b = 1 := mul_self_eq_one_of_orderOf h.orderOf_eq

theorem IsBabyCover.b_ne_one : b ≠ 1 := ne_one_of_orderOf h.orderOf_eq

theorem IsBabyCover.mem_zpowers_iff {y : G} :
    y ∈ Subgroup.zpowers b ↔ y = 1 ∨ y = b :=
  mem_zpowers_iff_of_orderOf_eq_two h.orderOf_eq

theorem IsBabyCover.coverMap_eq_one_iff {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ y = 1 ↔ y = 1 ∨ y = b := by
  rw [← h.mem_zpowers_iff, ← h.ker_eq, coverMap_apply hy]
  constructor
  · intro hφy
    exact ⟨⟨y, hy⟩, hφy, rfl⟩
  · rintro ⟨k, hk, hky⟩
    have : k = ⟨y, hy⟩ := Subtype.ext hky
    rw [this] at hk
    exact hk

theorem IsBabyCover.coverMap_b : coverMap φ b = 1 :=
  (h.coverMap_eq_one_iff (mem_centralizer_self b)).mpr (Or.inr rfl)

theorem IsBabyCover.coverMap_mul_b {y : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ (b * y) = coverMap φ y := by
  rw [coverMap_mul (mem_centralizer_self b) hy, h.coverMap_b, one_mul]

theorem IsBabyCover.coverMap_eq_iff {x y : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverMap φ x = coverMap φ y ↔ y = x ∨ y = b * x := by
  have hyx : y * x⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hx)
  have key : coverMap φ x = coverMap φ y ↔ coverMap φ (y * x⁻¹) = 1 := by
    rw [coverMap_mul hy (Subgroup.inv_mem _ hx), coverMap_inv hx, mul_inv_eq_one, eq_comm]
  rw [key, h.coverMap_eq_one_iff hyx, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem IsBabyCover.exists_coverMap_eq (s : B) :
    ∃ c ∈ Subgroup.centralizer ({b} : Set G), coverMap φ c = s := by
  obtain ⟨c, rfl⟩ := h.surjective s
  exact ⟨c, c.2, coverMap_apply c.2⟩

end Basic

section Pre

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

@[expose] def coverPre (φ : Subgroup.centralizer ({b} : Set G) →* B) (T : Subgroup B) :
    Subgroup G :=
  (T.comap φ).map (Subgroup.centralizer ({b} : Set G)).subtype

theorem mem_coverPre {T : Subgroup B} {g : G} :
    g ∈ coverPre φ T ↔ g ∈ Subgroup.centralizer ({b} : Set G) ∧ coverMap φ g ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    change coverMap φ (x : G) ∈ T
    rw [coverMap_apply x.2]
    exact hx
  · rintro ⟨hg, hT⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [coverMap_apply hg] at hT
    exact hT

theorem coverPre_le_centralizer (T : Subgroup B) :
    coverPre φ T ≤ Subgroup.centralizer ({b} : Set G) := fun _ hg => (mem_coverPre.mp hg).1

theorem coverPre_inf (S T : Subgroup B) :
    coverPre φ (S ⊓ T) = coverPre φ S ⊓ coverPre φ T := by
  ext g
  simp only [mem_coverPre, Subgroup.mem_inf]
  tauto

theorem card_coverPre [Finite G] (h : IsBabyCover b φ) (T : Subgroup B) :
    Nat.card (coverPre φ T) = 2 * Nat.card T := by
  have hker : Nat.card φ.ker = 2 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.centralizer ({b} : Set G)).subtype_injective,
      h.ker_eq, Nat.card_zpowers, h.orderOf_eq]
  have h1 : Nat.card (T.comap φ) * (T.comap φ).index =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := Subgroup.card_mul_index _
  have h2 : Nat.card T * T.index = Nat.card B := Subgroup.card_mul_index _
  have h3 : (T.comap φ).index = T.index := Subgroup.index_comap_of_surjective T h.surjective
  have h4 : Nat.card (Subgroup.centralizer ({b} : Set G)) = 2 * Nat.card B := by
    rw [← hker]
    exact (Subgroup.card_ker_mul_card_of_surjective h.surjective).symm
  have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [coverPre,
    Subgroup.card_map_of_injective (Subgroup.centralizer ({b} : Set G)).subtype_injective]
  rw [h3] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h4, mul_assoc, h2]

theorem mem_coverPre_centralizer_iff (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) {g : G} :
    g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)) ↔
      g ∈ Subgroup.centralizer ({b} : Set G) ∧ (g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x) := by
  rw [mem_coverPre]
  refine and_congr_right fun hg => ?_
  have hgx : g * x * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  rw [Subgroup.mem_centralizer_singleton_iff, ← h.coverMap_eq_iff hx hgx, coverMap_conj hg hx,
    eq_mul_inv_iff_mul_eq]
  exact eq_comm

theorem mem_coverPre_inf_centralizer_iff (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    {g : G} :
    g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
        Subgroup.centralizer ({coverMap φ y} : Set B)) ↔
      g ∈ Subgroup.centralizer ({b} : Set G) ∧ (g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x) ∧
        (g * y * g⁻¹ = y ∨ g * y * g⁻¹ = b * y) := by
  rw [coverPre_inf, Subgroup.mem_inf, mem_coverPre_centralizer_iff h hx,
    mem_coverPre_centralizer_iff h hy]
  tauto

end Pre

section Orbits

theorem card_inf_centralizer_mul_orbit (H : Subgroup G) (y : G) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({y} : Set G)) *
      {z : G | ∃ g ∈ H, g * y * g⁻¹ = z}.ncard = Nat.card H := by
  rw [← index_subgroupOf_centralizer_eq_ncard, inf_comm, mul_comm]
  exact Subgroup.relIndex_mul_card (Subgroup.centralizer ({y} : Set G)) H

theorem ncard_orbit_eq_two {H : Subgroup G} {b x : G} (hb : b ≠ 1) {g₀ : G} (hg₀ : g₀ ∈ H)
    (he : g₀ * x * g₀⁻¹ = b * x)
    (hsub : ∀ g ∈ H, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x) :
    {z : G | ∃ g ∈ H, g * x * g⁻¹ = z}.ncard = 2 := by
  have : {z : G | ∃ g ∈ H, g * x * g⁻¹ = z} = {x, b * x} := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hsub g hg
    · rintro (rfl | rfl)
      · exact ⟨1, H.one_mem, by simp⟩
      · exact ⟨g₀, hg₀, he⟩
  rw [this, Set.ncard_pair]
  intro hxb
  apply hb
  have : b * x = 1 * x := by rw [one_mul]; exact hxb.symm
  exact mul_right_cancel this

theorem ncard_orbit_eq_one {H : Subgroup G} {x : G} (hall : ∀ g ∈ H, g * x * g⁻¹ = x) :
    {z : G | ∃ g ∈ H, g * x * g⁻¹ = z}.ncard = 1 := by
  have : {z : G | ∃ g ∈ H, g * x * g⁻¹ = z} = {x} := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hall g hg
    · rintro rfl
      exact ⟨1, H.one_mem, by simp⟩
  rw [this, Set.ncard_singleton]

theorem ncard_orbit_eq_one_or_two {H : Subgroup G} {b x : G} (hb : b ≠ 1)
    (hsub : ∀ g ∈ H, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x) :
    {z : G | ∃ g ∈ H, g * x * g⁻¹ = z}.ncard = 1 ∨
      {z : G | ∃ g ∈ H, g * x * g⁻¹ = z}.ncard = 2 := by
  by_cases hyes : ∃ g ∈ H, g * x * g⁻¹ = b * x
  · obtain ⟨g₀, hg₀, he⟩ := hyes
    exact Or.inr (ncard_orbit_eq_two hb hg₀ he hsub)
  · push Not at hyes
    refine Or.inl (ncard_orbit_eq_one fun g hg => ?_)
    rcases hsub g hg with h | h
    · exact h
    · exact absurd h (hyes g hg)

end Orbits

section Index

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

theorem coverPre_centralizer_inf (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)) ⊓
        Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, mem_coverPre_centralizer_iff h hx]
  constructor
  · rintro ⟨⟨hg, -⟩, hgx⟩
    exact ⟨hg, hgx⟩
  · rintro ⟨hg, hgx⟩
    refine ⟨⟨hg, Or.inl ?_⟩, hgx⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgx
    rw [hgx, mul_inv_cancel_right]

theorem card_inf_centralizer_mul_orbit_coverPre [Finite G] (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) *
        {z : G | ∃ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)),
          g * x * g⁻¹ = z}.ncard =
      2 * Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B)) := by
  have := card_inf_centralizer_mul_orbit
    (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B))) x
  rwa [coverPre_centralizer_inf h hx, card_coverPre h] at this

theorem card_inf_centralizer_of_exists [Finite G] (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hyes : ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * x * g⁻¹ = b * x) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B)) := by
  obtain ⟨g₀, hg₀, he⟩ := hyes
  have hsub : ∀ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)),
      g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x := fun g hg =>
    ((mem_coverPre_centralizer_iff h hx).mp hg).2
  have h2 := ncard_orbit_eq_two h.b_ne_one
    ((mem_coverPre_centralizer_iff h hx).mpr ⟨hg₀, Or.inr he⟩) he hsub
  have := card_inf_centralizer_mul_orbit_coverPre h hx
  rw [h2] at this
  omega

theorem card_inf_centralizer_of_forall [Finite G] (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (hno : ∀ g ∈ Subgroup.centralizer ({b} : Set G), g * x * g⁻¹ ≠ b * x) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      2 * Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B)) := by
  have h1 := ncard_orbit_eq_one (H := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)))
    (x := x) fun g hg => by
      obtain ⟨hgb, hg'⟩ := (mem_coverPre_centralizer_iff h hx).mp hg
      rcases hg' with e | e
      · exact e
      · exact absurd e (hno g hgb)
  have := card_inf_centralizer_mul_orbit_coverPre h hx
  rw [h1] at this
  omega

theorem centralizer_inf_le_coverPre (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)) := by
  intro g hg
  refine (mem_coverPre_centralizer_iff h hx).mpr ⟨hg.1, Or.inl ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]

theorem relIndex_centralizer_inf_coverPre {x : G} :
    (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
        (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B))) =
      {z : G | ∃ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)),
        g * x * g⁻¹ = z}.ncard := by
  rw [← index_subgroupOf_centralizer_eq_ncard, Subgroup.relIndex]
  congr 1
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hg => hg.2, fun hg => ⟨coverPre_le_centralizer _ g.2, hg⟩⟩

theorem relIndex_centralizer_inf_coverPre_eq_two_iff (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
        (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B))) = 2 ↔
      ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * x * g⁻¹ = b * x := by
  have hsub : ∀ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)),
      g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x := fun g hg =>
    ((mem_coverPre_centralizer_iff h hx).mp hg).2
  rw [relIndex_centralizer_inf_coverPre]
  constructor
  · intro h2
    by_contra hno
    push Not at hno
    have h1 := ncard_orbit_eq_one (H := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B)))
      (x := x) fun g hg => (hsub g hg).resolve_right (hno g (coverPre_le_centralizer _ hg))
    omega
  · rintro ⟨g₀, hg₀, he⟩
    exact ncard_orbit_eq_two h.b_ne_one
      ((mem_coverPre_centralizer_iff h hx).mpr ⟨hg₀, Or.inr he⟩) he hsub

theorem relIndex_centralizer_inf_coverPre_eq_one_or_two (h : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
        (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B))) = 1 ∨
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
        (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B))) = 2 := by
  rw [relIndex_centralizer_inf_coverPre]
  exact ncard_orbit_eq_one_or_two h.b_ne_one fun g hg =>
    ((mem_coverPre_centralizer_iff h hx).mp hg).2

theorem coverPre_inf_centralizer_inf (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
          Subgroup.centralizer ({coverMap φ y} : Set B)) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, mem_coverPre_inf_centralizer_iff h hx hy]
  constructor
  · rintro ⟨⟨⟨hg, -⟩, hgx⟩, hgy⟩
    exact ⟨⟨hg, hgx⟩, hgy⟩
  · rintro ⟨⟨hg, hgx⟩, hgy⟩
    refine ⟨⟨⟨hg, Or.inl ?_, Or.inl ?_⟩, hgx⟩, hgy⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hgx
      rw [hgx, mul_inv_cancel_right]
    · rw [Subgroup.mem_centralizer_singleton_iff] at hgy
      rw [hgy, mul_inv_cancel_right]

theorem card_inf_inf_mul_orbit [Finite G] (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)) *
        ({z : G | ∃ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
              Subgroup.centralizer ({coverMap φ y} : Set B)) ⊓ Subgroup.centralizer ({x} : Set G),
            g * y * g⁻¹ = z}.ncard *
          {z : G | ∃ g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
              Subgroup.centralizer ({coverMap φ y} : Set B)), g * x * g⁻¹ = z}.ncard) =
      2 * Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
        Subgroup.centralizer ({coverMap φ y} : Set B)) := by
  set P := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
    Subgroup.centralizer ({coverMap φ y} : Set B)) with hP
  have h1 := card_inf_centralizer_mul_orbit (P ⊓ Subgroup.centralizer ({x} : Set G)) y
  have h2 := card_inf_centralizer_mul_orbit P x
  rw [hP, coverPre_inf_centralizer_inf h hx hy] at h1
  rw [← hP] at h1
  rw [← mul_assoc, h1, h2, hP, card_coverPre h]

section Pattern

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

noncomputable def patternBit (x g : G) : ZMod 2 := by
  classical exact if g * x * g⁻¹ = x then 0 else 1

theorem patternBit_mul (h : IsBabyCover b φ) {x g₁ g₂ : G}
    (hg₁ : g₁ ∈ Subgroup.centralizer ({b} : Set G))
    (h₁ : g₁ * x * g₁⁻¹ = x ∨ g₁ * x * g₁⁻¹ = b * x)
    (h₂ : g₂ * x * g₂⁻¹ = x ∨ g₂ * x * g₂⁻¹ = b * x) :
    patternBit x (g₁ * g₂) = patternBit x g₁ + patternBit x g₂ := by
  classical
  have hbx : b * x ≠ x := fun e => h.b_ne_one (by simpa using e)
  have hxb : x ≠ b * x := fun e => hbx e.symm
  have hconj : g₁ * g₂ * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
  have hbb : b * (b * x) = x := by rw [← mul_assoc, h.mul_self_b, one_mul]
  unfold patternBit
  rcases h₂ with e₂ | e₂
  · rw [hconj, e₂]
    by_cases e₁ : g₁ * x * g₁⁻¹ = x <;> simp [e₁]
  · have hconj' : g₁ * (b * x) * g₁⁻¹ = b * (g₁ * x * g₁⁻¹) :=
      conj_mul_of_mem_centralizer hg₁ x
    rw [hconj, e₂, hconj']
    rcases h₁ with e₁ | e₁
    · simp [e₁, hbx]
    · simp [e₁, hbb, hbx]
      decide

noncomputable def patternMap (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ y} : Set B)) →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := Multiplicative.ofAdd (patternBit x g, patternBit y g)
  map_one' := by
    classical
    simp [patternBit]
  map_mul' g₁ g₂ := by
    obtain ⟨hg₁, hx₁, hy₁⟩ := (mem_coverPre_inf_centralizer_iff h hx hy).mp g₁.2
    obtain ⟨-, hx₂, hy₂⟩ := (mem_coverPre_inf_centralizer_iff h hx hy).mp g₂.2
    show Multiplicative.ofAdd (patternBit x (g₁ * g₂ : G), patternBit y (g₁ * g₂ : G)) =
      Multiplicative.ofAdd (patternBit x g₁, patternBit y g₁) *
        Multiplicative.ofAdd (patternBit x g₂, patternBit y g₂)
    rw [← ofAdd_add, Prod.mk_add_mk, patternBit_mul h hg₁ hx₁ hx₂, patternBit_mul h hg₁ hy₁ hy₂]

theorem patternBit_eq_zero_iff {x g : G} : patternBit x g = 0 ↔ g * x * g⁻¹ = x := by
  classical
  unfold patternBit
  split_ifs with hg
  · simp [hg]
  · simp [hg]

theorem mem_centralizer_singleton_iff_conj {x g : G} :
    g ∈ Subgroup.centralizer ({x} : Set G) ↔ g * x * g⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro e
    rw [e, mul_inv_cancel_right]
  · intro e
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [e]

theorem mem_ker_patternMap (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (g : coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ y} : Set B))) :
    g ∈ (patternMap h hx hy).ker ↔
      (g : G) ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨hgb, -, -⟩ := (mem_coverPre_inf_centralizer_iff h hx hy).mp g.2
  rw [MonoidHom.mem_ker]
  have : patternMap h hx hy g = Multiplicative.ofAdd (patternBit x g, patternBit y g) := rfl
  rw [this, ← ofAdd_zero, Equiv.apply_eq_iff_eq, Prod.mk_eq_zero, patternBit_eq_zero_iff,
    patternBit_eq_zero_iff]
  have hgb' := mem_centralizer_singleton_iff_conj.mp hgb
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff_conj]
  tauto

theorem map_ker_patternMap (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    (patternMap h hx hy).ker.map (coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
        Subgroup.centralizer ({coverMap φ y} : Set B))).subtype =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (mem_ker_patternMap h hx hy g').mp hg'
  · intro hg
    have hgP : g ∈ coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
        Subgroup.centralizer ({coverMap φ y} : Set B)) := by
      refine (mem_coverPre_inf_centralizer_iff h hx hy).mpr ⟨hg.1.1, Or.inl ?_, Or.inl ?_⟩
      · exact mem_centralizer_singleton_iff_conj.mp hg.1.2
      · exact mem_centralizer_singleton_iff_conj.mp hg.2
    exact ⟨⟨g, hgP⟩, (mem_ker_patternMap h hx hy ⟨g, hgP⟩).mpr hg, rfl⟩

theorem card_inf_inf_mul_card_range [Finite G] (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hy : y ∈ Subgroup.centralizer ({b} : Set G)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) * Nat.card (patternMap h hx hy).range =
      2 * Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
        Subgroup.centralizer ({coverMap φ y} : Set B)) := by
  have h1 := Subgroup.card_ker_mul_card_range (patternMap h hx hy)
  rw [← card_coverPre h, ← map_ker_patternMap h hx hy,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact h1

end Pattern

end Index

section Fiber

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

theorem ncard_coverMap_preimage [Finite G] (h : IsBabyCover b φ) (T : Set B) :
    {c : G | c ∈ Subgroup.centralizer ({b} : Set G) ∧ coverMap φ c ∈ T}.ncard =
      2 * T.ncard := by
  obtain ⟨σ, hσ⟩ : ∃ σ : B → Subgroup.centralizer ({b} : Set G), ∀ s, φ (σ s) = s :=
    ⟨Function.surjInv h.surjective, Function.surjInv_eq h.surjective⟩
  have hker : Nat.card φ.ker = 2 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.centralizer ({b} : Set G)).subtype_injective,
      h.ker_eq, Nat.card_zpowers, h.orderOf_eq]
  have hF : {c : G | c ∈ Subgroup.centralizer ({b} : Set G) ∧ coverMap φ c ∈ T} =
      Subtype.val '' (φ ⁻¹' T) := by
    ext c
    constructor
    · rintro ⟨hc, hT⟩
      rw [coverMap_apply hc] at hT
      exact ⟨⟨c, hc⟩, hT, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      rw [coverMap_apply u.2]
      exact hu
  let e : (φ ⁻¹' T : Set (Subgroup.centralizer ({b} : Set G))) ≃ T × φ.ker :=
    { toFun := fun u => (⟨φ u.1, u.2⟩, ⟨(σ (φ u.1))⁻¹ * u.1, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]⟩)
      invFun := fun p => ⟨σ p.1 * p.2, by
        show φ (σ p.1 * p.2) ∈ T
        rw [map_mul, hσ, MonoidHom.mem_ker.mp p.2.2, mul_one]
        exact p.1.2⟩
      left_inv := fun u => by
        apply Subtype.ext
        simp
      right_inv := fun p => by
        have hφ : φ (σ p.1 * p.2) = p.1 := by
          rw [map_mul, hσ, MonoidHom.mem_ker.mp p.2.2, mul_one]
        refine Prod.ext (Subtype.ext hφ) (Subtype.ext ?_)
        show (σ (φ (σ p.1 * p.2)))⁻¹ * (σ p.1 * p.2) = p.2
        rw [hφ]
        simp }
  rw [hF, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    Nat.card_congr e, Nat.card_prod, hker, Nat.card_coe_set_eq]
  ring

end Fiber

section Baby

theorem BabyInv.of_isConj {k : Fin 4} {s t : B} (h : BabyInv k s) (hst : IsConj s t) :
    BabyInv k t :=
  ⟨(orderOf_eq_of_isConj hst).symm.trans h.1, (card_centralizer_eq_of_isConj hst).symm.trans h.2⟩

theorem babyCentOrder_injective : Function.Injective babyCentOrder := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [babyCentOrder] at h ⊢

theorem BabyInv.unique {k l : Fin 4} {t : B} (hk : BabyInv k t) (hl : BabyInv l t) : k = l :=
  babyCentOrder_injective (hk.2.symm.trans hl.2)

theorem tableVOrderB_eq_iff (k : Fin 4) : tableVOrderB = babyCentOrder k ↔ k = 0 := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderB]

theorem tableVOrderB_ne_two_mul (k : Fin 4) : tableVOrderB ≠ 2 * babyCentOrder k := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderB]

theorem tableVOrderZ_eq_two_mul_iff (k : Fin 4) : tableVOrderZ = 2 * babyCentOrder k ↔ k = 1 := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderZ]

theorem tableVOrderZ_ne (k : Fin 4) : tableVOrderZ ≠ babyCentOrder k := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderZ]

theorem tableVOrderU_eq_iff (k : Fin 4) : tableVOrderU = babyCentOrder k ↔ k = 2 := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderU]

theorem tableVOrderU_ne_two_mul (k : Fin 4) : tableVOrderU ≠ 2 * babyCentOrder k := by
  fin_cases k <;> simp [babyCentOrder, tableVOrderU]

end Baby

section TableVCover

variable {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

private theorem TableV.b_mem {a b z u : G} (h : TableV a b z u) :
    b ∈ Subgroup.centralizer ({a} : Set G) := h.1

private theorem TableV.b_orderOf {a b z u : G} (h : TableV a b z u) : orderOf b = 2 := h.2.2.2.1

private theorem TableV.b_ne {a b z u : G} (h : TableV a b z u) : b ≠ a := h.2.2.2.2.2.2.1

theorem IsBabyCover.orderOf_coverMap (h : IsBabyCover b φ) {t : G}
    (ht : t ∈ Subgroup.centralizer ({b} : Set G)) (ht2 : orderOf t = 2) (htb : t ≠ b) :
    orderOf (coverMap φ t) = 2 := by
  apply orderOf_eq_two_of_mul_self
  · rw [← coverMap_mul ht ht, mul_self_eq_one_of_orderOf ht2, coverMap_one]
  · intro h1
    rcases (h.coverMap_eq_one_iff ht).mp h1 with h2 | h2
    · exact ne_one_of_orderOf ht2 h2
    · exact htb h2

theorem IsBabyCover.exists_babyInv_cases [Finite G] (h : IsBabyCover b φ) (hT3 : BabyTableIII)
    {t : G} (ht : t ∈ Subgroup.centralizer ({b} : Set G)) (ht2 : orderOf t = 2) (htb : t ≠ b) :
    ∃ k, BabyInv k (coverMap φ t) ∧
      (((∃ g ∈ Subgroup.centralizer ({b} : Set G), g * t * g⁻¹ = b * t) ∧
          Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
            babyCentOrder k) ∨
        ((∀ g ∈ Subgroup.centralizer ({b} : Set G), g * t * g⁻¹ ≠ b * t) ∧
          Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
            2 * babyCentOrder k)) := by
  obtain ⟨k, hk⟩ := hT3.1 _ (h.orderOf_coverMap ht ht2 htb)
  refine ⟨k, hk, ?_⟩
  by_cases hyes : ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * t * g⁻¹ = b * t
  · exact Or.inl ⟨hyes, (card_inf_centralizer_of_exists h ht hyes).trans hk.2⟩
  · push Not at hyes
    exact Or.inr ⟨hyes, (card_inf_centralizer_of_forall h ht hyes).trans (by rw [hk.2])⟩

theorem IsBabyCover.babyInv_zero_of_tableV [Finite G] (h : IsBabyCover b φ) (hT3 : BabyTableIII)
    {b' z' u' : G} (hV : TableV b b' z' u') :
    BabyInv 0 (coverMap φ b') ∧
      ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * b' * g⁻¹ = b * b' := by
  obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 hV.b_mem hV.b_orderOf hV.b_ne
  have hcard := hV.card_b
  rcases hcase with ⟨hyes, hc⟩ | ⟨-, hc⟩
  · rw [hcard] at hc
    have : k = 0 := (tableVOrderB_eq_iff k).mp hc
    subst this
    exact ⟨hk, hyes⟩
  · rw [hcard] at hc
    exact absurd hc (tableVOrderB_ne_two_mul k)

theorem IsBabyCover.babyInv_one_of_tableV [Finite G] (h : IsBabyCover b φ) (hT3 : BabyTableIII)
    {b' z' u' : G} (hV : TableV b b' z' u') :
    BabyInv 1 (coverMap φ z') ∧
      ∀ g ∈ Subgroup.centralizer ({b} : Set G), g * z' * g⁻¹ ≠ b * z' := by
  obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 hV.mem_z hV.orderOf_z hV.ne_z
  have hcard := hV.card_z
  rcases hcase with ⟨-, hc⟩ | ⟨hno, hc⟩
  · rw [hcard] at hc
    exact absurd hc (tableVOrderZ_ne k)
  · rw [hcard] at hc
    have : k = 1 := (tableVOrderZ_eq_two_mul_iff k).mp hc
    subst this
    exact ⟨hk, hno⟩

theorem IsBabyCover.babyInv_two_of_tableV [Finite G] (h : IsBabyCover b φ) (hT3 : BabyTableIII)
    {b' z' u' : G} (hV : TableV b b' z' u') : BabyInv 2 (coverMap φ u') := by
  obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 hV.mem_u hV.orderOf_u hV.ne_u
  have hcard := hV.card_u
  rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
  · rw [hcard] at hc
    have : k = 2 := (tableVOrderU_eq_iff k).mp hc
    subst this
    exact hk
  · rw [hcard] at hc
    exact absurd hc (tableVOrderU_ne_two_mul k)

theorem IsBabyCover.babyInv_of_involution [Finite G] (h : IsBabyCover b φ) (hT3 : BabyTableIII)
    {b' z' u' : G} (hV : TableV b b' z' u') {t : G}
    (ht : t ∈ Subgroup.centralizer ({b} : Set G)) (ht2 : orderOf t = 2) (htb : t ≠ b) :
    BabyInv 0 (coverMap φ t) ∨ BabyInv 1 (coverMap φ t) ∨ BabyInv 2 (coverMap φ t) := by
  obtain ⟨g, hg, hcase⟩ := hV.cover t ht ht2 htb
  have hconj : IsConj (coverMap φ t) (coverMap φ (g * t * g⁻¹)) := by
    rw [coverMap_conj hg ht]
    exact isConj_iff.mpr ⟨coverMap φ g, rfl⟩
  have key : ∀ k, BabyInv k (coverMap φ (g * t * g⁻¹)) → BabyInv k (coverMap φ t) := fun k hk =>
    hk.of_isConj hconj.symm
  rcases hcase with e | e | e | e
  · rw [e] at hconj
    exact Or.inl (key 0 (by rw [e]; exact (h.babyInv_zero_of_tableV hT3 hV).1))
  · exact Or.inr (Or.inl (key 1 (by rw [e]; exact (h.babyInv_one_of_tableV hT3 hV).1)))
  · refine Or.inr (Or.inl (key 1 ?_))
    rw [e, h.coverMap_mul_b hV.mem_z]
    exact (h.babyInv_one_of_tableV hT3 hV).1
  · exact Or.inr (Or.inr (key 2 (by rw [e]; exact h.babyInv_two_of_tableV hT3 hV)))

theorem IsBabyCover.mul_self_eq_of_babyInv_three [Finite G] (h : IsBabyCover b φ)
    (hT3 : BabyTableIII) {b' z' u' : G} (hV : TableV b b' z' u') {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h3 : BabyInv 3 (coverMap φ x)) :
    x * x = b := by
  have hsq : coverMap φ (x * x) = 1 := by
    rw [coverMap_mul hx hx]
    exact mul_self_eq_one_of_orderOf (G := B) h3.1
  rcases (h.coverMap_eq_one_iff (Subgroup.mul_mem _ hx hx)).mp hsq with h1 | h1
  · exfalso
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [coverMap_one] at h3
      exact absurd h3.1 (by simp)
    have hxb : x ≠ b := by
      rintro rfl
      rw [h.coverMap_b] at h3
      exact absurd h3.1 (by simp)
    have hx2 : orderOf x = 2 := orderOf_eq_two_of_mul_self h1 hx1
    rcases h.babyInv_of_involution hT3 hV hx hx2 hxb with h0 | h0 | h0
    · exact absurd (h0.unique h3) (by decide)
    · exact absurd (h0.unique h3) (by decide)
    · exact absurd (h0.unique h3) (by decide)
  · exact h1

end TableVCover

section TableIV

theorem BabyOrbit.conj {k : Fin 4} {r q : B} (hk : BabyOrbit k r q) {g : B}
    (hg : g ∈ Subgroup.centralizer ({r} : Set B)) : BabyOrbit k r (g * q * g⁻¹) := by
  have hgr' : g * r = r * g := (Subgroup.mem_centralizer_singleton_iff (G := B)).mp hg
  have hgr : g * r * g⁻¹ = r := by rw [hgr', mul_inv_cancel_right]
  have hrq : r * (g * q * g⁻¹) = g * (r * q) * g⁻¹ := by
    calc r * (g * q * g⁻¹) = (g * r * g⁻¹) * (g * q * g⁻¹) := by rw [hgr]
      _ = g * (r * q) * g⁻¹ := (conj_mul_conj g r q).symm
  have hpow : ∀ n : ℕ, (r * (g * q * g⁻¹)) ^ n = g * (r * q) ^ n * g⁻¹ := by
    intro n
    rw [hrq, conj_pow]
  fin_cases k
  · change BabyInv 1 (r * (g * q * g⁻¹))
    rw [hrq]
    exact BabyInv.of_isConj hk (isConj_conj_self (G := B) g _)
  · change BabyInv 3 (r * (g * q * g⁻¹))
    rw [hrq]
    exact BabyInv.of_isConj hk (isConj_conj_self (G := B) g _)
  · change orderOf (r * (g * q * g⁻¹)) = 3
    rw [hrq, orderOf_conj_eq]
    exact hk
  · obtain ⟨h1, h2⟩ := hk
    refine ⟨?_, ?_⟩
    · rw [hrq, orderOf_conj_eq]
      exact h1
    · rw [hpow]
      exact BabyInv.of_isConj h2 (isConj_conj_self (G := B) g _)

theorem not_babyOrbit_self {k : Fin 4} {r : B} (hr : BabyInv 0 r) : ¬ BabyOrbit k r r := by
  have h1 : r * r = 1 := mul_self_eq_one_of_orderOf (G := B) hr.1
  fin_cases k
  · change ¬ BabyInv 1 (r * r)
    rw [h1]
    exact fun h => by simpa using h.1
  · change ¬ BabyInv 3 (r * r)
    rw [h1]
    exact fun h => by simpa using h.1
  · change ¬ orderOf (r * r) = 3
    rw [h1]
    simp
  · change ¬ (orderOf (r * r) = 4 ∧ BabyInv 1 ((r * r) ^ 2))
    rw [h1]
    exact fun h => by simpa using h.1

theorem BabyTableIV.card_inf_mul (hT4 : BabyTableIV) {r s : B} (hr : BabyInv 0 r)
    (hs : BabyInv 0 s) {k : Fin 4} (hk : BabyOrbit k r s) :
    Nat.card ↥(Subgroup.centralizer ({r} : Set B) ⊓ Subgroup.centralizer ({s} : Set B)) *
      babyOrbitSize k = babyCentOrder 0 := by
  obtain ⟨-, htr, hsize⟩ := hT4 r hr
  have h := card_inf_centralizer_mul_ncard (G := B) (H := Subgroup.centralizer ({r} : Set B))
    (Y := {s | BabyInv 0 s ∧ BabyOrbit k r s})
    (fun g hg q hq => ⟨hq.1.of_isConj (isConj_conj_self (G := B) g q), hq.2.conj hg⟩)
    (fun q hq q' hq' => htr k q q' hq.1 hq'.1 hq.2 hq'.2) (q := s) ⟨hs, hk⟩
  rw [hsize k, hr.2] at h
  exact h

end TableIV

end Generic

section TwoCover

variable {G : Type} [Group G]

theorem TwoClasses.conj {a z₀ b z u : G} (h : TwoClasses a z₀ b z u) (c : G) :
    TwoClasses (c * a * c⁻¹) z₀ (c * b * c⁻¹) (c * z * c⁻¹) (c * u * c⁻¹) where
  tableV := h.tableV.conj c
  orderOf_a := by rw [orderOf_conj_eq]; exact h.orderOf_a
  orderOf_z₀ := h.orderOf_z₀
  not_isConj := fun hc => h.not_isConj ((isConj_conj_self c a).trans hc)
  isConj_b := isConj_conj_conj c h.isConj_b
  isConj_z := h.isConj_z.trans (isConj_conj_self c z)
  isConj_az := by
    have : c * a * c⁻¹ * (c * z * c⁻¹) = c * (a * z) * c⁻¹ := by group
    rw [this]
    exact isConj_conj_conj c h.isConj_az
  mem_leechQ_z := conj_mem_leechQ_conj h.mem_leechQ_z
  isConj_u := h.isConj_u.trans (isConj_conj_self c u)
  isConj_au := by
    have : c * a * c⁻¹ * (c * u * c⁻¹) = c * (a * u) * c⁻¹ := by group
    rw [this]
    exact h.isConj_au.trans (isConj_conj_self c _)
  not_mem_leechQ_u := by
    intro hQ
    apply h.not_mem_leechQ_u
    rw [mem_leechQ_conj_iff] at hQ
    have : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    rwa [this] at hQ
  card_u := (card_leechQ_inf_centralizer_conj c u a).trans h.card_u
  gms := h.gms
  leech := h.leech

theorem TwoClasses.exists_of_isConj {a z₀ b₀ z u b : G} (h : TwoClasses a z₀ b₀ z u)
    (hb : IsConj a b) : ∃ b' z' u' : G, TwoClasses b z₀ b' z' u' := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hb
  exact ⟨_, _, _, hg ▸ h.conj g⟩

theorem twoANbr_congr {a b : G} (hab : IsConj a b) (x : G) : twoANbr a x = twoANbr b x := by
  ext y
  exact and_congr ⟨fun hy => hab.symm.trans hy, fun hy => hab.trans hy⟩
    ⟨fun hy => hab.symm.trans hy, fun hy => hab.trans hy⟩

theorem TwoClasses.exists_conj_of_mem_twoANbr_self {z₀ b b' z' u' : G}
    (hB : TwoClasses b z₀ b' z' u') {y : G} (hy : y ∈ twoANbr b b) :
    y ∈ Subgroup.centralizer ({b} : Set G) ∧
      ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * y * g⁻¹ = b' := by
  obtain ⟨hc, hbc⟩ := hy
  have hb2 := hB.orderOf_a
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf hb2
  have hc2 : orderOf y = 2 := (orderOf_eq_of_isConj hc).symm.trans hb2
  have hbc2 : orderOf (b * y) = 2 := (orderOf_eq_of_isConj hbc).symm.trans hb2
  have hcomm : b * y = y * b :=
    mul_comm_of_mul_self_eq_one hbb (mul_self_eq_one_of_orderOf hc2)
      (mul_self_eq_one_of_orderOf hbc2)
  have hyC : y ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  refine ⟨hyC, ?_⟩
  have hyb : y ≠ b := by
    rintro rfl
    have : orderOf (y * y) = 2 := hbc2
    rw [mul_self_eq_one_of_orderOf hc2, orderOf_one] at this
    omega
  obtain ⟨g, hg, hcase⟩ := hB.tableV.cover y hyC hc2 hyb
  rcases hcase with e | e | e | e
  · exact ⟨g, hg, e⟩
  · exact absurd ((hc.trans (isConj_iff.mpr ⟨g, e⟩)).trans hB.isConj_z.symm) hB.not_isConj
  · have hgbc : g * (b * y) * g⁻¹ = b * (g * y * g⁻¹) := conj_mul_of_mem_centralizer hg y
    have : g * (b * y) * g⁻¹ = z' := by rw [hgbc, e, ← mul_assoc, hbb, one_mul]
    exact absurd ((hbc.trans (isConj_iff.mpr ⟨g, this⟩)).trans hB.isConj_z.symm) hB.not_isConj
  · exact absurd ((hc.trans (isConj_iff.mpr ⟨g, e⟩)).trans hB.isConj_u.symm) hB.not_isConj

theorem TwoClasses.exists_conj_of_mem_twoANbr {a z₀ b₀ z u b : G} (h : TwoClasses a z₀ b₀ z u)
    (hb : IsConj a b) {y₁ y₂ : G} (h₁ : y₁ ∈ twoANbr a b) (h₂ : y₂ ∈ twoANbr a b) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * y₁ * g⁻¹ = y₂ := by
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj hb
  rw [twoANbr_congr hb] at h₁ h₂
  obtain ⟨-, g₁, hg₁, e₁⟩ := hB.exists_conj_of_mem_twoANbr_self h₁
  obtain ⟨-, g₂, hg₂, e₂⟩ := hB.exists_conj_of_mem_twoANbr_self h₂
  refine ⟨g₂⁻¹ * g₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₂) hg₁, ?_⟩
  have e₂' : y₂ = g₂⁻¹ * b' * g₂ := by rw [← e₂]; group
  rw [e₂', ← e₁]
  group

theorem TwoClasses.card_centralizer_inf_of_mem_twoANbr {a z₀ b₀ z u x y : G}
    (h : TwoClasses a z₀ b₀ z u) (hx : IsConj a x) (hy : y ∈ twoANbr a x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) =
      tableVOrderB := by
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj hx
  rw [twoANbr_congr hx] at hy
  obtain ⟨-, g, hg, e⟩ := hB.exists_conj_of_mem_twoANbr_self hy
  rw [← card_inf_centralizer_conj hg y, e]
  exact hB.tableV.card_b

section Cover

variable {G : Type} [Group G] [Finite G] {z₀ b b' z' u' : G}
  {φ : Subgroup.centralizer ({b} : Set G) →* B}

theorem TwoClasses.exists_conj_of_babyInv_zero (hB : TwoClasses b z₀ b' z' u')
    (hT3 : BabyTableIII) (hφ : IsBabyCover b φ) {c : G}
    (hcC : c ∈ Subgroup.centralizer ({b} : Set G)) (hc0 : BabyInv 0 (coverMap φ c)) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * c * g⁻¹ = b' := by
  obtain ⟨hb0, g₂, hg₂, he₂⟩ := hφ.babyInv_zero_of_tableV hT3 hB.tableV
  obtain ⟨d, hd⟩ := isConj_iff.mp (hT3.2 0 _ _ hb0 hc0)
  obtain ⟨g₁, hg₁, hgd⟩ := hφ.exists_coverMap_eq d
  have hb'C : b' ∈ Subgroup.centralizer ({b} : Set G) := hB.tableV.b_mem
  have hy : g₁ * b' * g₁⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hb'C) (Subgroup.inv_mem _ hg₁)
  have hmap : coverMap φ c = coverMap φ (g₁ * b' * g₁⁻¹) := by
    rw [coverMap_conj hg₁ hb'C, hgd]
    exact hd.symm
  rcases (hφ.coverMap_eq_iff hcC hy).mp hmap with e | e
  · refine ⟨g₁⁻¹, Subgroup.inv_mem _ hg₁, ?_⟩
    rw [← e]
    group
  · have hc : c = g₁ * (g₂ * b' * g₂⁻¹) * g₁⁻¹ := by
      calc c = b * (b * c) := by rw [← mul_assoc, hφ.mul_self_b, one_mul]
        _ = b * (g₁ * b' * g₁⁻¹) := by rw [e]
        _ = g₁ * (b * b') * g₁⁻¹ := (conj_mul_of_mem_centralizer hg₁ b').symm
        _ = g₁ * (g₂ * b' * g₂⁻¹) * g₁⁻¹ := by rw [he₂]
    refine ⟨(g₁ * g₂)⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ hg₁ hg₂), ?_⟩
    rw [hc]
    group

theorem TwoClasses.exists_conj_of_babyInv_one (hB : TwoClasses b z₀ b' z' u')
    (hT3 : BabyTableIII) (hφ : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h1 : BabyInv 1 (coverMap φ x)) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G),
      g * x * g⁻¹ = z' ∨ g * x * g⁻¹ = b * z' := by
  have hz1 := (hφ.babyInv_one_of_tableV hT3 hB.tableV).1
  obtain ⟨d, hd⟩ := isConj_iff.mp (hT3.2 1 _ _ hz1 h1)
  obtain ⟨g₁, hg₁, hgd⟩ := hφ.exists_coverMap_eq d
  have hz'C : z' ∈ Subgroup.centralizer ({b} : Set G) := hB.tableV.mem_z
  have hy : g₁ * z' * g₁⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hz'C) (Subgroup.inv_mem _ hg₁)
  have hmap : coverMap φ x = coverMap φ (g₁ * z' * g₁⁻¹) := by
    rw [coverMap_conj hg₁ hz'C, hgd]
    exact hd.symm
  rcases (hφ.coverMap_eq_iff hx hy).mp hmap with e | e
  · exact ⟨g₁⁻¹, Subgroup.inv_mem _ hg₁, Or.inl (by rw [← e]; group)⟩
  · have hxe : x = g₁ * (b * z') * g₁⁻¹ := by
      calc x = b * (b * x) := by rw [← mul_assoc, hφ.mul_self_b, one_mul]
        _ = b * (g₁ * z' * g₁⁻¹) := by rw [e]
        _ = g₁ * (b * z') * g₁⁻¹ := (conj_mul_of_mem_centralizer hg₁ z').symm
    exact ⟨g₁⁻¹, Subgroup.inv_mem _ hg₁, Or.inr (by rw [hxe]; group)⟩

theorem TwoClasses.isConj_mul_b (hB : TwoClasses b z₀ b' z' u') (hT3 : BabyTableIII)
    (hφ : IsBabyCover b φ) : IsConj b (b * b') := by
  obtain ⟨g, -, hg⟩ := (hφ.babyInv_zero_of_tableV hT3 hB.tableV).2
  exact hB.isConj_b.trans (isConj_iff.mpr ⟨g, hg⟩)

theorem TwoClasses.mem_twoANbr_self_iff (hB : TwoClasses b z₀ b' z' u') (hT3 : BabyTableIII)
    (hφ : IsBabyCover b φ) {c : G} :
    c ∈ twoANbr b b ↔
      c ∈ Subgroup.centralizer ({b} : Set G) ∧ BabyInv 0 (coverMap φ c) := by
  constructor
  · intro hc
    obtain ⟨hcC, g, hg, e⟩ := hB.exists_conj_of_mem_twoANbr_self hc
    refine ⟨hcC, ?_⟩
    have h0 := (hφ.babyInv_zero_of_tableV hT3 hB.tableV).1
    have h1 : BabyInv 0 (coverMap φ (g * c * g⁻¹)) := by rw [e]; exact h0
    rw [coverMap_conj hg hcC] at h1
    exact h1.of_isConj (isConj_conj_self (G := B) _ _).symm
  · rintro ⟨hcC, hc0⟩
    obtain ⟨g, hg, hgc⟩ := hB.exists_conj_of_babyInv_zero hT3 hφ hcC hc0
    have hgi : g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.inv_mem _ hg
    have hc : c = g⁻¹ * b' * g := by rw [← hgc]; group
    refine ⟨hB.isConj_b.trans (isConj_iff.mpr ⟨g, hgc⟩).symm, ?_⟩
    have hbc : b * c = g⁻¹ * (b * b') * g := by
      have := conj_mul_of_mem_centralizer hgi b'
      rw [inv_inv] at this
      rw [this, hc]
    rw [hbc]
    exact (hB.isConj_mul_b hT3 hφ).trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)

theorem TwoClasses.babyInv_one_cases_self (hB : TwoClasses b z₀ b' z' u') (hT3 : BabyTableIII)
    (hφ : IsBabyCover b φ) {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G))
    (h1 : BabyInv 1 (coverMap φ x)) :
    x * x = 1 ∧ ((IsConj z₀ x ∧ IsConj b (b * x)) ∨ (IsConj b x ∧ IsConj z₀ (b * x))) := by
  obtain ⟨g, hg, hcase⟩ := hB.exists_conj_of_babyInv_one hT3 hφ hx h1
  have hzz : z' * z' = 1 := mul_self_eq_one_of_orderOf hB.tableV.orderOf_z
  have hbzz : (b * z') * (b * z') = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hB.isConj_az).symm.trans hB.orderOf_a)
  rcases hcase with e | e
  · refine ⟨?_, Or.inl ⟨hB.isConj_z.trans (isConj_iff.mpr ⟨g, e⟩).symm, ?_⟩⟩
    · calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = 1 := by rw [e, hzz]; group
    · have : g * (b * x) * g⁻¹ = b * z' := by rw [conj_mul_of_mem_centralizer hg x, e]
      exact hB.isConj_az.trans (isConj_iff.mpr ⟨g, this⟩).symm
  · refine ⟨?_, Or.inr ⟨hB.isConj_az.trans (isConj_iff.mpr ⟨g, e⟩).symm, ?_⟩⟩
    · calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = 1 := by rw [e, hbzz]; group
    · have : g * (b * x) * g⁻¹ = z' := by
        rw [conj_mul_of_mem_centralizer hg x, e, ← mul_assoc, hφ.mul_self_b, one_mul]
      exact hB.isConj_z.trans (isConj_iff.mpr ⟨g, this⟩).symm

end Cover

section CoverA

variable {G : Type} [Group G] [Finite G] {a z₀ b₀ z u b : G}
  {φ : Subgroup.centralizer ({b} : Set G) →* B}

theorem TwoClasses.mem_twoANbr_iff (h : TwoClasses a z₀ b₀ z u) (hT3 : BabyTableIII)
    (hb : IsConj a b) (hφ : IsBabyCover b φ) {c : G} :
    c ∈ twoANbr a b ↔ c ∈ Subgroup.centralizer ({b} : Set G) ∧ BabyInv 0 (coverMap φ c) := by
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj hb
  rw [twoANbr_congr hb]
  exact hB.mem_twoANbr_self_iff hT3 hφ

theorem TwoClasses.babyInv_one_cases (h : TwoClasses a z₀ b₀ z u) (hT3 : BabyTableIII)
    (hb : IsConj a b) (hφ : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h1 : BabyInv 1 (coverMap φ x)) :
    x * x = 1 ∧ ((IsConj z₀ x ∧ IsConj a (b * x)) ∨ (IsConj a x ∧ IsConj z₀ (b * x))) := by
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj hb
  obtain ⟨hxx, hcase⟩ := hB.babyInv_one_cases_self hT3 hφ hx h1
  refine ⟨hxx, ?_⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, hb.trans h2⟩
  · exact Or.inr ⟨hb.trans h1, h2⟩

theorem TwoClasses.mul_self_eq_of_babyInv_three (h : TwoClasses a z₀ b₀ z u)
    (hT3 : BabyTableIII) (hb : IsConj a b) (hφ : IsBabyCover b φ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h3 : BabyInv 3 (coverMap φ x)) :
    x * x = b := by
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj hb
  exact hφ.mul_self_eq_of_babyInv_three hT3 hB.tableV hx h3

end CoverA

section Setting

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem isTwoBabyCentralizer_of_isConj (hSLS : SLSStatement d₀) {a z₀ b : G}
    (hG : GMSF1Type d₀ a z₀) (hb : IsConj a b) : IsTwoBabyCentralizer b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hb
  have := (hG.1.isTwoBabyCentralizer hSLS).of_mulEquiv (MulAut.conj g)
  rwa [MulAut.conj_apply, hg] at this

theorem exists_twoClasses_of_isConj
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ b : G} (hG : GMSF1Type d₀ a z₀) (hb : IsConj a b) :
    ∃ b' z' u' : G, TwoClasses b z₀ b' z' u' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.exists_of_isConj hb

theorem mem_twoANbr_iff (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {b : G}
    (hb : IsConj a b) {φ : Subgroup.centralizer ({b} : Set G) →* B} (hφ : IsBabyCover b φ)
    {c : G} :
    c ∈ twoANbr a b ↔ c ∈ Subgroup.centralizer ({b} : Set G) ∧ BabyInv 0 (coverMap φ c) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.mem_twoANbr_iff hT3 hb hφ

theorem babyInv_one_cases (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {b : G}
    (hb : IsConj a b) {φ : Subgroup.centralizer ({b} : Set G) →* B} (hφ : IsBabyCover b φ)
    {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h1 : BabyInv 1 (coverMap φ x)) :
    x * x = 1 ∧ ((IsConj z₀ x ∧ IsConj a (b * x)) ∨ (IsConj a x ∧ IsConj z₀ (b * x))) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.babyInv_one_cases hT3 hb hφ hx h1

theorem mul_self_eq_of_babyInv_three
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {b : G}
    (hb : IsConj a b) {φ : Subgroup.centralizer ({b} : Set G) →* B} (hφ : IsBabyCover b φ)
    {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (h3 : BabyInv 3 (coverMap φ x)) :
    x * x = b := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.mul_self_eq_of_babyInv_three hT3 hb hφ hx h3

theorem isConj_of_mem_twoANbr_self
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {b : G} (hb : IsConj a b)
    {y₁ y₂ : G} (h₁ : y₁ ∈ twoANbr a b) (h₂ : y₂ ∈ twoANbr a b) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G), g * y₁ * g⁻¹ = y₂ := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.exists_conj_of_mem_twoANbr hb h₁ h₂

end Setting

end TwoCover

end CFSG.Monster.GMS
