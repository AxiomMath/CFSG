module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Gen3 (A B : Subgroup D) (z : D) (V : Subgroup D) (x a a₁ a₂ : D) : Prop where
  hyp : GoldHyp3 A B z V
  x_mem : x ∈ B
  x_not : x ∉ A ⊓ B
  x2_not : x * x ∉ A ⊓ B
  x_cube : x * x * x = 1
  a_mem : a ∈ V
  a_ne_one : a ≠ 1
  a_ne_z : a ≠ z
  V_set : (V : Set D) = {1, z, a, z * a}
  a₁_eq : a₁ = x * a * x⁻¹
  a₂_eq : a₂ = x * x * a * (x * x)⁻¹

theorem GoldHyp3.exists_gen3 [Finite D] (h : GoldHyp3 A B z V) :
    ∃ x a a₁ a₂, Gen3 A B z V x a a₁ a₂ := by
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  obtain ⟨a, ha1, haz, hVset⟩ := h.natural.basis
  have hcube : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx3] at this
    simpa [pow_succ, mul_assoc] using this
  refine ⟨x, a, x * a * x⁻¹, x * x * a * (x * x)⁻¹,
    ⟨h, hxB, h.gold.vertex_right.not_mem_of_orderOf hx3,
    h.gold.vertex_right.sq_not_mem_of_orderOf hx3, hcube, ?_, ha1, haz, hVset, rfl, rfl⟩⟩
  have : a ∈ (V : Set D) := by rw [hVset]; simp
  exact this

namespace Gen3

variable {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

omit g in
theorem mem_V_iff (g : Gen3 A B z V x a a₁ a₂) {v : D} :
    v ∈ V ↔ v = 1 ∨ v = z ∨ v = a ∨ v = z * a := by
  have := Set.ext_iff.mp g.V_set v
  simpa using this

theorem conj_a₁ : x * a₁ * x⁻¹ = a₂ := by
  rw [g.a₁_eq, g.a₂_eq]; group

theorem conj_a₂ : x * a₂ * x⁻¹ = a := by
  rw [g.a₂_eq]
  calc x * (x * x * a * (x * x)⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
    _ = a := by rw [g.x_cube]; group

theorem conj_a : x * a * x⁻¹ = a₁ := g.a₁_eq.symm

theorem x2_mem : x * x ∈ B := B.mul_mem g.x_mem g.x_mem

theorem z_mul_z : z * z = 1 := by
  have := g.hyp.natural.z_sq
  rwa [pow_two] at this

theorem z_comm {b : D} (hb : b ∈ B) : b * z = z * b := mul_eq_of_conj_eq (g.hyp.central b hb)

theorem conj_z : x * z * x⁻¹ = z := g.hyp.central x g.x_mem

theorem a_sq : a * a = 1 := g.hyp.natural.mul_self_of_mem g.a_mem

theorem a₁_sq : a₁ * a₁ = 1 := by
  rw [g.a₁_eq]
  calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
    _ = 1 := by rw [g.a_sq]; group

theorem a₂_sq : a₂ * a₂ = 1 := by
  rw [g.a₂_eq]
  calc x * x * a * (x * x)⁻¹ * (x * x * a * (x * x)⁻¹) = (x * x) * (a * a) * (x * x)⁻¹ := by
        group
    _ = 1 := by rw [g.a_sq]; group

theorem a_mem_U : a ∈ conjClosure V B := le_conjClosure V B g.a_mem

theorem z_mem_U : z ∈ conjClosure V B := le_conjClosure V B g.hyp.natural.z_mem_V

theorem a₁_mem_U : a₁ ∈ conjClosure V B := by
  rw [g.a₁_eq]; exact mem_conjClosure g.x_mem g.a_mem

theorem a₂_mem_U : a₂ ∈ conjClosure V B := by
  rw [g.a₂_eq]; exact mem_conjClosure g.x2_mem g.a_mem

theorem U_comm {u w : D} (hu : u ∈ conjClosure V B) (hw : w ∈ conjClosure V B) :
    u * w = w * u := isElemAbelian_comm g.hyp.abelian hu hw

end Gen3

end GoldAmL3c

end F6

end CFSG.Quasithin
