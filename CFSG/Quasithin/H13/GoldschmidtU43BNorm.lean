module

public import CFSG.Quasithin.H13.GoldschmidtU43Count

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Vg (z t : G) : Subgroup G := Subgroup.closure {z, t}

structure Comm2 (z t : G) : Prop where
  sq_z : z * z = 1
  sq_t : t * t = 1
  comm : z * t = t * z

theorem zp_inv {z : G} (hz : z * z = 1) (a : ZMod 2) : (zp z a)⁻¹ = zp z a := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [zp_zero]
  · rw [zp_one]
    exact inv_eq_of_mul_eq_one_right hz

theorem conj_zp (g z : G) (a : ZMod 2) : g * zp z a * g⁻¹ = zp (g * z * g⁻¹) a := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [zp_zero]
  · simp [zp_one]

namespace Comm2

variable {z t : G} (hp : Comm2 z t)
include hp

theorem zp_comm (a b : ZMod 2) : zp z a * zp t b = zp t b * zp z a := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [zp_zero, zp_one, hp.comm]

theorem mem_Vg_iff (x : G) : x ∈ Vg z t ↔ ∃ a b : ZMod 2, x = zp z a * zp t b := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ⟨1, 0, by simp [zp_zero, zp_one]⟩
      · exact ⟨0, 1, by simp [zp_zero, zp_one]⟩
    | one => exact ⟨0, 0, by simp [zp_zero]⟩
    | mul y y' _ _ ih ih' =>
      obtain ⟨a, b, rfl⟩ := ih
      obtain ⟨c, d, rfl⟩ := ih'
      refine ⟨a + c, b + d, ?_⟩
      calc zp z a * zp t b * (zp z c * zp t d)
          = zp z a * (zp t b * zp z c) * zp t d := by group
        _ = zp z a * (zp z c * zp t b) * zp t d := by rw [← hp.zp_comm c b]
        _ = (zp z a * zp z c) * (zp t b * zp t d) := by group
        _ = zp z (a + c) * zp t (b + d) := by rw [zp_add hp.sq_z, zp_add hp.sq_t]
    | inv y _ ih =>
      obtain ⟨a, b, rfl⟩ := ih
      refine ⟨a, b, ?_⟩
      rw [mul_inv_rev, zp_inv hp.sq_z, zp_inv hp.sq_t, ← hp.zp_comm a b]
  · rintro ⟨a, b, rfl⟩
    refine mul_mem ?_ ?_
    · rcases zmod_two_cases a with rfl | rfl
      · rw [zp_zero]; exact one_mem _
      · rw [zp_one]; exact Subgroup.subset_closure (by simp)
    · rcases zmod_two_cases b with rfl | rfl
      · rw [zp_zero]; exact one_mem _
      · rw [zp_one]; exact Subgroup.subset_closure (by simp)

theorem mem_Vg_iff₄ (x : G) : x ∈ Vg z t ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  rw [hp.mem_Vg_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
      simp [zp_zero, zp_one]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp [zp_zero]⟩
    · exact ⟨1, 0, by simp [zp_zero, zp_one]⟩
    · exact ⟨0, 1, by simp [zp_zero, zp_one]⟩
    · exact ⟨1, 1, by simp [zp_one]⟩

theorem conj_mem_of_mem {g : G} (h1 : g * z * g⁻¹ ∈ Vg z t) (h2 : g * t * g⁻¹ ∈ Vg z t) {x : G}
    (hx : x ∈ Vg z t) : g * x * g⁻¹ ∈ Vg z t := by
  obtain ⟨a, b, rfl⟩ := (hp.mem_Vg_iff x).1 hx
  have : g * (zp z a * zp t b) * g⁻¹ = zp (g * z * g⁻¹) a * zp (g * t * g⁻¹) b := by
    rw [← conj_zp, ← conj_zp]
    group
  rw [this]
  refine mul_mem ?_ ?_
  · rcases zmod_two_cases a with rfl | rfl
    · rw [zp_zero]; exact one_mem _
    · rw [zp_one]; exact h1
  · rcases zmod_two_cases b with rfl | rfl
    · rw [zp_zero]; exact one_mem _
    · rw [zp_one]; exact h2

theorem mem_normalizer_Vg [Finite G] {g : G} (h1 : g * z * g⁻¹ ∈ Vg z t)
    (h2 : g * t * g⁻¹ ∈ Vg z t) : g ∈ Subgroup.normalizer (Vg z t : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨hp.conj_mem_of_mem h1 h2, fun hx => ?_⟩
  let φ : ↥(Vg z t) → ↥(Vg z t) := fun v => ⟨g * v * g⁻¹, hp.conj_mem_of_mem h1 h2 v.2⟩
  have hinj : Function.Injective φ := by
    intro v v' hvv
    have : g * (v : G) * g⁻¹ = g * (v' : G) * g⁻¹ := congrArg Subtype.val hvv
    exact Subtype.ext (by simpa using this)
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨g * x * g⁻¹, hx⟩
  have : g * (v : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hv
  have hvx : (v : G) = x := by simpa using this
  rw [← hvx]
  exact v.2

end Comm2

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem comm2 {t : G} (ht : t ∈ S z) : Comm2 z t := ⟨h.sq_z, ht.2.1, h.z_comm ht.1⟩

theorem exists_swap' [Finite G] {t : G} (ht : t ∈ S z) :
    ∃ w : G, w⁻¹ * z * w = t ∧ w⁻¹ * t * w = z ∧
      ∀ x : G, x ∈ Uz z ⊓ CFSG.conjugate (Uz z) w ↔ x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  obtain ⟨t₀, w₀, ht₀U, ht₀z, ht₀1, ht₀2, hw1, hw2, hI⟩ := h.exists_swap
  obtain ⟨x, hxH, hx⟩ := h.exists_conj ht₀U ht₀1 ht₀z ht₀2 ht.1 ht.2.2.1 ht.2.2.2 ht.2.1
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxH
  have hxz' : x⁻¹ * z * x = z := by
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  have h2 : x * z * x⁻¹ = z := by
    calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hxz]
      _ = z := by group
  have hxU : ∀ a, x * a * x⁻¹ ∈ Uz z ↔ a ∈ Uz z := fun a =>
    (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hxH) a).symm
  have hy : ∀ y a : G, x⁻¹ * y * x = a ↔ y = x * a * x⁻¹ := by
    intro y a
    constructor
    · intro e
      rw [← e]
      group
    · intro e
      rw [e]
      group
  refine ⟨x * w₀ * x⁻¹, ?_, ?_, ?_⟩
  · calc (x * w₀ * x⁻¹)⁻¹ * z * (x * w₀ * x⁻¹) = x * (w₀⁻¹ * (x⁻¹ * z * x) * w₀) * x⁻¹ := by group
      _ = x * (w₀⁻¹ * z * w₀) * x⁻¹ := by rw [hxz']
      _ = t := by rw [hw1, hx]
  · calc (x * w₀ * x⁻¹)⁻¹ * t * (x * w₀ * x⁻¹)
        = x * (w₀⁻¹ * (x⁻¹ * t * x) * w₀) * x⁻¹ := by group
      _ = x * (w₀⁻¹ * t₀ * w₀) * x⁻¹ := by rw [(hy t t₀).2 hx.symm]
      _ = z := by rw [hw2, h2]
  · intro y
    rw [Subgroup.mem_inf, mem_conjugate_iff]
    have key : (y ∈ Uz z ∧ (x * w₀ * x⁻¹) * y * (x * w₀ * x⁻¹)⁻¹ ∈ Uz z) ↔
        (x⁻¹ * y * x ∈ Uz z ⊓ CFSG.conjugate (Uz z) w₀) := by
      rw [Subgroup.mem_inf, mem_conjugate_iff]
      have e1 : y ∈ Uz z ↔ x⁻¹ * y * x ∈ Uz z := by
        rw [← hxU (x⁻¹ * y * x)]
        simp [mul_assoc]
      have e2 : (x * w₀ * x⁻¹) * y * (x * w₀ * x⁻¹)⁻¹ ∈ Uz z ↔
          w₀ * (x⁻¹ * y * x) * w₀⁻¹ ∈ Uz z := by
        rw [← hxU (w₀ * (x⁻¹ * y * x) * w₀⁻¹)]
        have : x * (w₀ * (x⁻¹ * y * x) * w₀⁻¹) * x⁻¹ =
            (x * w₀ * x⁻¹) * y * (x * w₀ * x⁻¹)⁻¹ := by group
        rw [this]
      rw [e1, e2]
    rw [key, hI]
    simp only [hy y 1, hy y z, hy y t₀, hy y (z * t₀)]
    have h1 : x * (1 : G) * x⁻¹ = 1 := by group
    have h3 : x * (z * t₀) * x⁻¹ = z * t := by
      calc x * (z * t₀) * x⁻¹ = (x * z * x⁻¹) * (x * t₀ * x⁻¹) := by group
        _ = z * t := by rw [h2, hx]
    rw [h1, h2, h3, hx]

end Hyp

end CFSG.Quasithin.H13.U43
