module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Monster.Schur

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure IsExtraspecialAmbient (P : Subgroup G) (z : G) : Prop where
  mem : z ∈ P
  ne_one : z ≠ 1
  central : ∀ g ∈ P, g * z = z * g
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a ∨ a * b = z * (b * a)
  center : ∀ g ∈ P, (∀ h ∈ P, g * h = h * g) → g = 1 ∨ g = z

namespace IsExtraspecialAmbient

variable {P : Subgroup G} {z : G} (hP : IsExtraspecialAmbient P z)
include hP

theorem mul_self : z * z = 1 := by
  have h := hP.center (z * z) (P.mul_mem hP.mem hP.mem) fun h hh => by
    have hzh : z * h = h * z := (hP.central h hh).symm
    calc z * z * h = z * (z * h) := mul_assoc _ _ _
      _ = z * (h * z) := by rw [hzh]
      _ = (z * h) * z := (mul_assoc _ _ _).symm
      _ = (h * z) * z := by rw [hzh]
      _ = h * (z * z) := mul_assoc _ _ _
  rcases h with h | h
  · exact h
  · exact absurd (mul_eq_left.1 h) hP.ne_one

theorem comm_dichotomy {x u c : G} (hx : x ∈ P) (hu : u ∈ P) (hc : c ∈ P)
    (hcx : c * x ≠ x * c) :
    (u * x = x * u ∧ ¬ (u * c) * x = x * (u * c)) ∨
      (¬ u * x = x * u ∧ (u * c) * x = x * (u * c)) := by
  by_cases hux : u * x = x * u
  · left
    refine ⟨hux, fun h => hcx ?_⟩
    have : u * (c * x) = u * (x * c) := by
      calc u * (c * x) = (u * c) * x := (mul_assoc _ _ _).symm
        _ = x * (u * c) := h
        _ = (x * u) * c := (mul_assoc _ _ _).symm
        _ = (u * x) * c := by rw [hux]
        _ = u * (x * c) := mul_assoc _ _ _
    exact mul_left_cancel this
  · right
    refine ⟨hux, ?_⟩
    have h1 : u * x = z * (x * u) := (hP.comm u hu x hx).resolve_left hux
    have h2 : c * x = z * (x * c) := (hP.comm c hc x hx).resolve_left hcx
    have hzu : u * z = z * u := hP.central u hu
    have hz2 := hP.mul_self
    calc (u * c) * x = u * (c * x) := mul_assoc _ _ _
      _ = u * (z * (x * c)) := by rw [h2]
      _ = (u * z) * (x * c) := (mul_assoc _ _ _).symm
      _ = (z * u) * (x * c) := by rw [hzu]
      _ = z * ((u * x) * c) := by simp only [mul_assoc]
      _ = z * ((z * (x * u)) * c) := by rw [h1]
      _ = (z * z) * (x * (u * c)) := by simp only [mul_assoc]
      _ = x * (u * c) := by rw [hz2, one_mul]

theorem two_mul_card_inf_centralizer [Finite P] {B : Subgroup G} (hBP : B ≤ P) {x : G}
    (hx : x ∈ P) (hne : ∃ b ∈ B, b * x ≠ x * b) :
    2 * Nat.card ↥(B ⊓ centralizer {x}) = Nat.card ↥B := by
  obtain ⟨b₀, hb₀, hb₀x⟩ := hne
  have hidx : ((B ⊓ centralizer {x}).subgroupOf B).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b₀, hb₀⟩, fun b => ?_⟩
    have hd := hP.comm_dichotomy hx (hBP b.2) (hBP hb₀) hb₀x
    have hmem : ∀ w : B, w ∈ (B ⊓ centralizer {x}).subgroupOf B ↔ (w : G) * x = x * w := by
      intro w
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
    rw [hmem, hmem]
    simp only [Subgroup.coe_mul]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
  have h := Subgroup.card_mul_index ((B ⊓ centralizer {x}).subgroupOf B)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv] at h
  omega

end IsExtraspecialAmbient

open Classical in
theorem sum_ite_mul_comm_eq_card (B : Subgroup G) [Fintype B] (x : G) :
    (∑ b : B, if (b : G) * x = x * b then 1 else 0) = Nat.card ↥(B ⊓ centralizer {x}) := by
  rw [← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_singleton_iff.2 b.2⟩
      invFun := fun b => ⟨⟨b.1, b.2.1⟩, Subgroup.mem_centralizer_singleton_iff.1 b.2.2⟩
      left_inv := fun b => rfl
      right_inv := fun b => rfl }

namespace IsExtraspecialAmbient

variable {P : Subgroup G} {z : G} (hP : IsExtraspecialAmbient P z)
include hP

open Classical in
theorem card_inf_centralizer_mul_card [Finite P] {A : Subgroup G} (hAP : A ≤ P) (hzA : z ∈ A) :
    Nat.card ↥(P ⊓ centralizer (A : Set G)) * Nat.card ↥A = 2 * Nat.card ↥P := by
  have : Fintype P := Fintype.ofFinite _
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAP) (Subgroup.inclusion_injective hAP)
  have : Fintype A := Fintype.ofFinite _
  have hrow : ∀ a : A, 2 * (∑ p : P, if (a : G) * p = p * a then 1 else 0) =
      Nat.card P + (if ((a : G) = 1 ∨ (a : G) = z) then Nat.card P else 0) := by
    intro a
    have e : (∑ p : P, if (a : G) * p = p * a then 1 else 0) =
        ∑ p : P, if (p : G) * a = a * p then 1 else 0 :=
      Finset.sum_congr rfl fun p _ => if_congr eq_comm rfl rfl
    rw [e, sum_ite_mul_comm_eq_card P (a : G)]
    by_cases ha : (a : G) = 1 ∨ (a : G) = z
    · rw [ite_eq_left ha]
      have : P ⊓ centralizer {(a : G)} = P := by
        refine inf_eq_left.2 fun g hg => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases ha with ha | ha
        · rw [ha, one_mul, mul_one]
        · rw [ha]; exact hP.central g hg
      rw [this]
      omega
    · rw [ite_eq_right ha]
      obtain ⟨h, hh, hne⟩ : ∃ h ∈ P, h * (a : G) ≠ (a : G) * h := by
        by_contra hcon
        push Not at hcon
        exact ha (hP.center a (hAP a.2) fun h hh => (hcon h hh).symm)
      have := hP.two_mul_card_inf_centralizer le_rfl (hAP a.2) ⟨h, hh, hne⟩
      omega
  have hcol : ∀ p : P, 2 * (∑ a : A, if (a : G) * p = p * a then 1 else 0) =
      Nat.card A + (if (∀ a ∈ A, a * (p : G) = p * a) then Nat.card A else 0) := by
    intro p
    rw [sum_ite_mul_comm_eq_card A (p : G)]
    by_cases hp : ∀ a ∈ A, a * (p : G) = p * a
    · rw [ite_eq_left hp]
      have : A ⊓ centralizer {(p : G)} = A := by
        refine inf_eq_left.2 fun g hg => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hp g hg
      rw [this]
      omega
    · rw [ite_eq_right hp]
      obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a * (p : G) ≠ p * a := by
        by_contra hcon
        push Not at hcon
        exact hp hcon
      have := hP.two_mul_card_inf_centralizer hAP p.2 ⟨a, ha, hne⟩
      omega
  have hsum : (∑ a : A, ∑ p : P, if (a : G) * p = p * a then 1 else 0) =
      ∑ p : P, ∑ a : A, if (a : G) * p = p * a then 1 else 0 := Finset.sum_comm
  have hZ : (Finset.univ.filter fun a : A => (a : G) = 1 ∨ (a : G) = z).card = 2 := by
    rw [Finset.card_eq_two]
    refine ⟨1, ⟨z, hzA⟩, fun h => hP.ne_one ?_, ?_⟩
    · exact (congrArg Subtype.val h).symm
    · ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · rintro (h | h)
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
  have hC : (Finset.univ.filter fun p : P => ∀ a ∈ A, a * (p : G) = p * a).card =
      Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1, p.1.2, Subgroup.mem_centralizer_iff.2 fun a ha => p.2 a ha⟩
        invFun := fun p => ⟨⟨p.1, p.2.1⟩, fun a ha => Subgroup.mem_centralizer_iff.1 p.2.2 a ha⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
  have h2 : 2 * (∑ a : A, ∑ p : P, if (a : G) * p = p * a then 1 else 0) =
      Nat.card A * Nat.card P + 2 * Nat.card P := by
    rw [Finset.mul_sum]
    simp only [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hZ]
    simp [Nat.card_eq_fintype_card]
  have h2' : 2 * (∑ p : P, ∑ a : A, if (a : G) * p = p * a then 1 else 0) =
      Nat.card P * Nat.card A + Nat.card ↥(P ⊓ centralizer (A : Set G)) * Nat.card A := by
    rw [Finset.mul_sum]
    simp only [hcol, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hC]
    simp [Nat.card_eq_fintype_card]
  have h3 := h2.symm.trans ((congrArg (2 * ·) hsum).trans h2')
  rw [mul_comm (Nat.card P) (Nat.card A)] at h3
  omega

theorem exists_mem_centralizer_not_mem_of_lt [Finite P] {A₁ A₂ : Subgroup G} (hA₂P : A₂ ≤ P)
    (hzA₁ : z ∈ A₁) (hlt : A₁ < A₂) :
    ∃ v ∈ P, (∀ a ∈ A₁, a * v = v * a) ∧ ∃ a ∈ A₂, a * v ≠ v * a := by
  by_contra hcon
  have hA₁P : A₁ ≤ P := hlt.le.trans hA₂P
  have : Finite A₂ := Finite.of_injective (Subgroup.inclusion hA₂P)
    (Subgroup.inclusion_injective hA₂P)
  have h1 := hP.card_inf_centralizer_mul_card hA₁P hzA₁
  have h2 := hP.card_inf_centralizer_mul_card hA₂P (hlt.le hzA₁)
  have hle : P ⊓ centralizer (A₂ : Set G) ≤ P ⊓ centralizer (A₁ : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hlt.le)
  have hge : P ⊓ centralizer (A₁ : Set G) ≤ P ⊓ centralizer (A₂ : Set G) := by
    intro v hv
    refine ⟨hv.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    by_contra hne
    exact hcon ⟨v, hv.1, fun a' ha' => Subgroup.mem_centralizer_iff.1 hv.2 a' ha', a, ha, hne⟩
  have hEq : P ⊓ centralizer (A₂ : Set G) = P ⊓ centralizer (A₁ : Set G) := le_antisymm hle hge
  rw [hEq] at h2
  have : Finite ↥(P ⊓ centralizer (A₁ : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card ↥(P ⊓ centralizer (A₁ : Set G)) := Nat.card_pos
  have := Subgroup.card_lt_of_lt hlt
  nlinarith

theorem exists_comm_not_comm [Finite P] {x u : G} (hx : x ∈ P) (hx1 : x ≠ 1) (hxz : x ≠ z)
    (hu : u ∈ P) (hu1 : u ≠ 1) (hux : u ≠ x) (huz : u ≠ z) (huxz : u ≠ x * z) :
    ∃ v ∈ P, v * x = x * v ∧ v * u ≠ u * v := by
  have hxc : ∃ b ∈ P, b * x ≠ x * b := by
    by_contra hcon
    push Not at hcon
    exact (hP.center x hx fun h hh => (hcon h hh).symm).elim hx1 hxz
  have hA : 2 * Nat.card ↥(P ⊓ centralizer {x}) = Nat.card ↥P :=
    hP.two_mul_card_inf_centralizer le_rfl hx hxc
  have hAP : P ⊓ centralizer {x} ≤ P := inf_le_left
  have hzA : z ∈ P ⊓ centralizer {x} :=
    ⟨hP.mem, Subgroup.mem_centralizer_singleton_iff.2 (hP.central x hx).symm⟩
  have hcard := hP.card_inf_centralizer_mul_card hAP hzA
  have : Finite ↥(P ⊓ centralizer {x}) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card ↥(P ⊓ centralizer {x}) := Nat.card_pos
  have hC4 : Nat.card ↥(P ⊓ centralizer ((P ⊓ centralizer {x} : Subgroup G) : Set G)) = 4 := by
    have h4 : Nat.card ↥(P ⊓ centralizer ((P ⊓ centralizer {x} : Subgroup G) : Set G)) *
        Nat.card ↥(P ⊓ centralizer {x}) = 4 * Nat.card ↥(P ⊓ centralizer {x}) := by
      rw [hcard]; omega
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  set C := P ⊓ centralizer ((P ⊓ centralizer {x} : Subgroup G) : Set G) with hCdef
  have hxC : x ∈ C := by
    refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 ha.2
  have hzC : z ∈ C := ⟨hP.mem, Subgroup.mem_centralizer_iff.2 fun a ha => hP.central a (hAP ha)⟩
  have hxzC : x * z ∈ C := C.mul_mem hxC hzC
  have hS : ({1, x, z, x * z} : Set G) ⊆ (C : Set G) := by
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact hxC
    · exact hzC
    · exact hxzC
  have hz1 := hP.ne_one
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hP.mul_self
  have hxz1 : x * z ≠ 1 := fun h => hxz (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, hzz])
  have h3 : z ≠ x * z := fun h => hx1 (by simpa using h.symm)
  have h2 : x ∉ ({z, x * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxz, fun h => hz1 (by simpa using h)⟩
  have h1 : (1 : G) ∉ ({x, z, x * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hx1 h.symm, fun h => hz1 h.symm, fun h => hxz1 h.symm⟩
  have hSc : ({1, x, z, x * z} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  have hCc : (C : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hC4
  have hCfin : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : C ≤ P)) (Subgroup.inclusion_injective _)
  have hSC : ({1, x, z, x * z} : Set G) = (C : Set G) :=
    Set.eq_of_subset_of_ncard_le hS (by rw [hSc, hCc]) (Set.toFinite _)
  have huC : u ∉ C := by
    intro huC
    have : u ∈ ({1, x, z, x * z} : Set G) := by rw [hSC]; exact huC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h | h
    · exact hu1 h
    · exact hux h
    · exact huz h
    · exact huxz h
  by_contra hcon
  push Not at hcon
  apply huC
  refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  exact hcon a (hAP ha) (Subgroup.mem_centralizer_singleton_iff.1 ha.2)

end IsExtraspecialAmbient

namespace IsExtraspecialAmbient

variable {P : Subgroup G} {z : G} (hP : IsExtraspecialAmbient P z)
include hP

theorem commute_inv_mul_of_not_commute {u t t' : G} (hu : u ∈ P) (ht : t ∈ P) (ht' : t' ∈ P)
    (h : u * t ≠ t * u) (h' : u * t' ≠ t' * u) : u * (t⁻¹ * t') = (t⁻¹ * t') * u := by
  have e1 : u * t = z * (t * u) := (hP.comm u hu t ht).resolve_left h
  have e2 : u * t' = z * (t' * u) := (hP.comm u hu t' ht').resolve_left h'
  have key : z * (t * (u * (t⁻¹ * t'))) = z * (t * ((t⁻¹ * t') * u)) := by
    calc z * (t * (u * (t⁻¹ * t'))) = (z * (t * u)) * (t⁻¹ * t') := by group
      _ = (u * t) * (t⁻¹ * t') := by rw [e1]
      _ = u * t' := by group
      _ = z * (t' * u) := e2
      _ = z * (t * ((t⁻¹ * t') * u)) := by group
  exact mul_left_cancel (mul_left_cancel key)

end IsExtraspecialAmbient

@[expose] def conjSub (g : G) (S : Subgroup G) : Subgroup G := S.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g : G} {S : Subgroup G} {h : G} : h ∈ conjSub g S ↔ g⁻¹ * h * g ∈ S := by
  rw [conjSub, Subgroup.mem_map_equiv]
  rfl

theorem natCard_conjSub (g : G) (S : Subgroup G) : Nat.card (conjSub g S) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mul_mem_conjSub {g : G} {S : Subgroup G} {s : G} (hs : s ∈ S) : g * s * g⁻¹ ∈ conjSub g S :=
  mem_conjSub.2 (by simpa [mul_assoc] using hs)

theorem conjSub_mono (g : G) {S T : Subgroup G} (h : S ≤ T) : conjSub g S ≤ conjSub g T :=
  fun _ hx => mem_conjSub.2 (h (mem_conjSub.1 hx))

namespace IsExtraspecialAmbient

variable {P : Subgroup G} {z : G} (hP : IsExtraspecialAmbient P z)
include hP

theorem conj (g : G) : IsExtraspecialAmbient (conjSub g P) (g * z * g⁻¹) where
  mem := mul_mem_conjSub hP.mem
  ne_one := fun h => hP.ne_one (by simpa using h)
  central := fun h hh => by
    have := hP.central _ (mem_conjSub.1 hh)
    calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = (g * z * g⁻¹) * h := by group
  comm := fun a ha b hb => by
    have ha' := mem_conjSub.1 ha
    have hb' := mem_conjSub.1 hb
    rcases hP.comm _ ha' _ hb' with h | h
    · left
      calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
        _ = b * a := by group
    · right
      calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * (z * ((g⁻¹ * b * g) * (g⁻¹ * a * g))) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * (b * a) := by group
  center := fun c hc hcen => by
    have hc' := mem_conjSub.1 hc
    rcases hP.center _ hc' (fun h hh => by
      have := hcen (g * h * g⁻¹) (mul_mem_conjSub hh)
      calc g⁻¹ * c * g * h = g⁻¹ * (c * (g * h * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * h * g⁻¹) * c) * g := by rw [this]
        _ = h * (g⁻¹ * c * g) := by group) with h | h
    · left
      have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      rw [this, h]
      group
    · right
      have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      rw [this, h]

end IsExtraspecialAmbient

theorem IsExtraspecialAmbient.of_isExtraspecialPGroup {P : Subgroup G} {z : G}
    (hP : IsExtraspecialPGroup 2 P) (hz : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ g ∈ P, g * z = z * g) :
    IsExtraspecialAmbient P z := by
  have hcard : Nat.card (Subgroup.center P) = 2 := hP.2.2.2
  have hzcen : (⟨z, hz⟩ : P) ∈ Subgroup.center P :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hzc g g.2)
  have hcenter : ∀ c ∈ Subgroup.center P, c = 1 ∨ c = ⟨z, hz⟩ := by
    intro c hc
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center P)).1 hcard
    by_cases h : c = 1
    · exact Or.inl h
    · right
      have h1 : (⟨c, hc⟩ : Subgroup.center P) = ⟨⟨z, hz⟩, hzcen⟩ :=
        (hw _ (fun e => h (congrArg Subtype.val e))).trans
          (hw ⟨⟨z, hz⟩, hzcen⟩ (fun e => hz1 (congrArg Subtype.val (congrArg Subtype.val e)))).symm
      exact congrArg Subtype.val h1
  refine ⟨hz, hz1, hzc, fun a ha b hb => ?_, fun g hg hgc => ?_⟩
  · have hmem : ⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ ∈ Subgroup.center P := by
      rw [← hP.2.1, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rcases hcenter _ hmem with h | h
    · left
      have h' : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h', one_mul]
    · right
      have h' : a * b * a⁻¹ * b⁻¹ = z := congrArg Subtype.val h
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = z * (b * a) := by rw [h']
  · have : (⟨g, hg⟩ : P) ∈ Subgroup.center P :=
      Subgroup.mem_center_iff.2 fun h => Subtype.ext (hgc h h.2).symm
    rcases hcenter _ this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

end CFSG.Monster.Schur
