module

public import CFSG.Monster.GMS.S4Defs

public section

namespace CFSG.Monster.GMS.S4Assembly

section IsoOn

variable {G G' : Type*} [Group G] [Group G'] {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}

theorem iso_map_one (h : IsIsoOn f H H') : f 1 = 1 := by
  have h1 : f 1 * f 1 = f 1 * 1 := by
    rw [← h.map_mul 1 H.one_mem 1 H.one_mem, mul_one, mul_one]
  exact mul_left_cancel h1

theorem iso_map_pow (h : IsIsoOn f H H') {x : G} (hx : x ∈ H) (n : ℕ) :
    f (x ^ n) = f x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, iso_map_one h]
  | succ n ih => rw [pow_succ, h.map_mul _ (H.pow_mem hx n) _ hx, ih, pow_succ]

theorem iso_orderOf (h : IsIsoOn f H H') {x : G} (hx : x ∈ H) : orderOf (f x) = orderOf x := by
  refine (orderOf_eq_orderOf_iff.2 fun n => ?_).symm
  rw [← iso_map_pow h hx n]
  constructor
  · intro hxn
    rw [hxn, iso_map_one h]
  · intro hxn
    exact h.injOn (H.pow_mem hx n) H.one_mem (hxn.trans (iso_map_one h).symm)

theorem iso_map_inv (h : IsIsoOn f H H') {x : G} (hx : x ∈ H) : f x⁻¹ = (f x)⁻¹ := by
  have := h.map_mul x hx x⁻¹ (H.inv_mem hx)
  rw [mul_inv_cancel, iso_map_one h] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem iso_map_conj (h : IsIsoOn f H H') {g x : G} (hg : g ∈ H) (hx : x ∈ H) :
    f (g * x * g⁻¹) = f g * f x * (f g)⁻¹ := by
  rw [h.map_mul _ (H.mul_mem hg hx) _ (H.inv_mem hg), h.map_mul _ hg _ hx, iso_map_inv h hg]

theorem iso_commute (h : IsIsoOn f H H') {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    f x * f y = f y * f x ↔ x * y = y * x := by
  rw [← h.map_mul x hx y hy, ← h.map_mul y hy x hx]
  exact ⟨fun e => h.injOn (H.mul_mem hx hy) (H.mul_mem hy hx) e, fun e => by rw [e]⟩

theorem iso_mem_centralizer_iff (h : IsIsoOn f H H') {s x : G} (hs : s ∈ H) (hx : x ∈ H) :
    f s ∈ Subgroup.centralizer ({f x} : Set G') ↔ s ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact iso_commute h hs hx

end IsoOn

section Centralizer

variable {G : Type*} [Group G]

theorem mem_centralizer_comm {x y : G} :
    x ∈ Subgroup.centralizer ({y} : Set G) ↔ y ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem self_mem_centralizer (x : G) : x ∈ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem conj_eq_of_mem_centralizer {s x : G} (hs : s ∈ Subgroup.centralizer ({x} : Set G)) :
    s * x * s⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs
  rw [hs]
  group

end Centralizer

end CFSG.Monster.GMS.S4Assembly
