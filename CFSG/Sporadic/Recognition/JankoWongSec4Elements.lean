module

public import CFSG.Sporadic.Recognition.JankoWongSec4Cover
public import CFSG.Sporadic.Recognition.JankoWongSec4Conj
public import CFSG.Sporadic.Recognition.JankoWongLemma15

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

structure Sec4Hyp (c : Ctx S) (a₁ v v₁ : G) : Prop where
  a1_mem : a₁ ∈ S.H
  v_mem : v ∈ S.H
  v1_mem : v₁ ∈ S.H
  a1_sq : a₁ ^ 2 = S.z
  rel : Sec4HRel (c.a : G) (c.t : G) a₁ v v₁

theorem Ctx.exists_sec4Hyp (c : Ctx S) : ∃ a₁ v v₁ : G, Sec4Hyp c a₁ v v₁ := by
  obtain ⟨a₁, v, v₁, -, -, -, ha1, hrel⟩ :=
    S.cover.exists_sec4_lifts (σ₁ := c.a) (u := c.t) c.ha c.ha3 c.ht c.ht2
  refine ⟨a₁, v, v₁, a₁.2, v.2, v₁.2, ?_, hrel.map S.H.subtype⟩
  have := congrArg Subtype.val ha1
  rw [Subgroup.coe_pow] at this
  exact this

namespace Ctx

variable (c : Ctx S)

theorem tG_inv : (c.t : G)⁻¹ = c.t :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact c.tG_sq')

theorem zG_inv : S.z⁻¹ = S.z :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact z_sq (S := S))

theorem zc {x : G} (hx : x ∈ S.H) : x * S.z = S.z * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

theorem tG_mem_H : (c.t : G) ∈ S.H := c.t.2
theorem aG_mem_H : (c.a : G) ∈ S.H := c.a.2
theorem bG_mem_H : (c.b : G) ∈ S.H := c.b.2

theorem cj_a_t : cj (c.a : G) (c.t : G) = (c.b : G) := by
  have h := congrArg Subtype.val c.t_conj_a
  have h' : (c.t : G) * (c.a : G) * (c.t : G)⁻¹ = (c.b : G) := by simpa using h
  rw [cj, c.tG_inv]
  rw [c.tG_inv] at h'
  exact h'

theorem cj_b_t : cj (c.b : G) (c.t : G) = (c.a : G) := by
  have h := congrArg Subtype.val c.t_conj_b
  have h' : (c.t : G) * (c.b : G) * (c.t : G)⁻¹ = (c.a : G) := by simpa using h
  rw [cj, c.tG_inv]
  rw [c.tG_inv] at h'
  exact h'

theorem a_comm_b : (c.a : G) * (c.b : G) = (c.b : G) * (c.a : G) := by
  have := congrArg Subtype.val c.hab
  simpa using this

theorem aG_cube' : (c.a : G) ^ 3 = 1 := c.aG_cube

theorem bG_cube : (c.b : G) ^ 3 = 1 := by
  have := congrArg Subtype.val c.hb3
  simpa using this

@[expose] def a2 (a₁ : G) : G := cj a₁ (c.t : G)

end Ctx

theorem inv_eq_mul_z_of_sq' (S : Setup G) {x : G} (hx : x ^ 2 = S.z) : x⁻¹ = x * S.z := by
  have h1 : x * x = S.z := by rwa [← pow_two]
  calc x⁻¹ = x⁻¹ * (x * x) * S.z⁻¹ := by rw [h1]; group
    _ = x * S.z⁻¹ := by group
    _ = x * S.z := by rw [Ctx.zG_inv (S := S)]

namespace Sec4Hyp

variable {c : Ctx S} {a₁ v v₁ : G} (h : Sec4Hyp c a₁ v v₁)
include h

theorem a2_mem : c.a2 a₁ ∈ S.H :=
  S.H.mul_mem (S.H.mul_mem (S.H.inv_mem c.t.2) h.a1_mem) c.t.2

theorem a1_comm_z : a₁ * S.z = S.z * a₁ := Ctx.zc h.a1_mem
theorem v_comm_z : v * S.z = S.z * v := Ctx.zc h.v_mem
theorem v1_comm_z : v₁ * S.z = S.z * v₁ := Ctx.zc h.v1_mem
theorem a2_comm_z : c.a2 a₁ * S.z = S.z * c.a2 a₁ := Ctx.zc h.a2_mem

theorem a2_sq : c.a2 a₁ ^ 2 = S.z := by
  have := h.rel.a2_sq
  rw [h.a1_sq] at this
  exact this

theorem v_sq : v ^ 2 = S.z := by
  have := h.rel.v_sq
  rw [h.a1_sq] at this
  exact this

theorem v1_sq : v₁ ^ 2 = S.z := by
  have := h.rel.v1_sq
  rw [h.a1_sq] at this
  exact this

theorem a1_inv : a₁⁻¹ = a₁ * S.z := inv_eq_mul_z_of_sq' S h.a1_sq
theorem a2_inv : (c.a2 a₁)⁻¹ = c.a2 a₁ * S.z := inv_eq_mul_z_of_sq' S h.a2_sq
theorem v_inv : v⁻¹ = v * S.z := inv_eq_mul_z_of_sq' S h.v_sq
theorem v1_inv : v₁⁻¹ = v₁ * S.z := inv_eq_mul_z_of_sq' S h.v1_sq

end Sec4Hyp

end Setup

end CFSG.Sporadic.Recognition.JankoWong
