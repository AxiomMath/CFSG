module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Gen (A B : Subgroup D) (z : D) (V : Subgroup D) (x a a₁ a₂ : D) : Prop
    extends Gen0 A B z V x a where
  a₁_eq : a₁ = x * a * x⁻¹
  a₂_eq : a₂ = x * x * a * (x * x)⁻¹

theorem B2Setup.exists_gen [Finite D] (s : B2Setup A B z V) :
    ∃ x a a₁ a₂ : D, Gen A B z V x a a₁ a₂ := by
  obtain ⟨x, a, g⟩ := s.exists_gen0
  exact ⟨x, a, _, _, ⟨g, rfl, rfl⟩⟩

namespace Gen

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem a₁_sq : a₁ * a₁ = 1 := by
  rw [g.a₁_eq]
  calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
    _ = 1 := by rw [g.a_sq]; group

theorem a₂_sq : a₂ * a₂ = 1 := by
  rw [g.a₂_eq]
  calc x * x * a * (x * x)⁻¹ * (x * x * a * (x * x)⁻¹) = (x * x) * (a * a) * (x * x)⁻¹ := by
        group
    _ = 1 := by rw [g.a_sq]; group

theorem conj_a₁ : x * a₁ * x⁻¹ = a₂ := by
  rw [g.a₁_eq, g.a₂_eq]; group

theorem conj_a₂ : x * a₂ * x⁻¹ = a := by
  rw [g.a₂_eq]
  calc x * (x * x * a * (x * x)⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
    _ = a := by rw [g.x_cube]; group

theorem a_mem_QB : a ∈ pCoreOf 2 B := g.setup.V_le g.a_mem

theorem a₁_mem_QB : a₁ ∈ pCoreOf 2 B := by
  rw [g.a₁_eq]
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B g.x_mem) a).mp g.a_mem_QB
  exact this

theorem a₂_mem_QB : a₂ ∈ pCoreOf 2 B := by
  rw [g.a₂_eq]
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B g.x2_mem) a).mp g.a_mem_QB
  exact this

theorem a_mem_U : a ∈ conjClosure V B := le_conjClosure V B g.a_mem

theorem a₁_mem_U : a₁ ∈ conjClosure V B := by
  rw [g.a₁_eq]; exact mem_conjClosure g.x_mem g.a_mem

theorem z_comm_a₁ : z * a₁ = a₁ * z :=
  (g.setup.z_comm (pCoreOf_le 2 B g.a₁_mem_QB)).symm

theorem z_comm_a₂ : z * a₂ = a₂ * z :=
  (g.setup.z_comm (pCoreOf_le 2 B g.a₂_mem_QB)).symm

variable [Finite D] in
theorem not_comm01 : a * a₁ ≠ a₁ * a := by
  rw [g.a₁_eq]; exact g.toGen0.not_comm

variable [Finite D] in
theorem comm01 : a * a₁ * a⁻¹ * a₁⁻¹ = z := by
  rcases g.setup.mem_zpowers (g.setup.comm_UU' g.a_mem_U g.a₁_mem_U) with h | h
  · exfalso
    apply g.not_comm01
    calc a * a₁ = (a * a₁ * a⁻¹ * a₁⁻¹) * (a₁ * a) := by group
      _ = a₁ * a := by rw [h, one_mul]
  · exact h

variable [Finite D] in
theorem r01 : a * a₁ = z * (a₁ * a) := by
  calc a * a₁ = (a * a₁ * a⁻¹ * a₁⁻¹) * (a₁ * a) := by group
    _ = z * (a₁ * a) := by rw [g.comm01]

variable [Finite D] in
theorem r12 : a₁ * a₂ = z * (a₂ * a₁) := by
  have h := congrArg (fun w => x * w * x⁻¹) g.r01
  calc a₁ * a₂ = x * (a * a₁) * x⁻¹ := by
        calc a₁ * a₂ = (x * a * x⁻¹) * (x * a₁ * x⁻¹) := by rw [← g.a₁_eq, g.conj_a₁]
          _ = x * (a * a₁) * x⁻¹ := by group
    _ = x * (z * (a₁ * a)) * x⁻¹ := h
    _ = (x * z * x⁻¹) * ((x * a₁ * x⁻¹) * (x * a * x⁻¹)) := by group
    _ = z * (a₂ * a₁) := by rw [g.conj_z, g.conj_a₁, ← g.a₁_eq]

variable [Finite D] in
theorem r20 : a₂ * a = z * (a * a₂) := by
  have h := congrArg (fun w => x * w * x⁻¹) g.r12
  calc a₂ * a = x * (a₁ * a₂) * x⁻¹ := by
        calc a₂ * a = (x * a₁ * x⁻¹) * (x * a₂ * x⁻¹) := by rw [g.conj_a₁, g.conj_a₂]
          _ = x * (a₁ * a₂) * x⁻¹ := by group
    _ = x * (z * (a₂ * a₁)) * x⁻¹ := h
    _ = (x * z * x⁻¹) * ((x * a₂ * x⁻¹) * (x * a₁ * x⁻¹)) := by group
    _ = z * (a * a₂) := by rw [g.conj_z, g.conj_a₂, g.conj_a₁]

variable [Finite D] in
theorem u_sq : a₁ * a₂ * (a₁ * a₂) = z := by
  calc a₁ * a₂ * (a₁ * a₂) = (a₁ * a₂) * a₁ * a₂ := by group
    _ = (z * (a₂ * a₁)) * a₁ * a₂ := by rw [g.r12]
    _ = z * a₂ * (a₁ * a₁) * a₂ := by group
    _ = z := by
      rw [g.a₁_sq]
      calc z * a₂ * 1 * a₂ = z * (a₂ * a₂) := by group
        _ = z := by rw [g.a₂_sq, mul_one]

variable [Finite D] in
theorem a₁_not_mem_QA : a₁ ∉ pCoreOf 2 A := fun h1 => g.not_comm01 <|
  (Subgroup.mem_centralizer_iff.mp (g.setup.natural.le_center g.a_mem).2 a₁ h1).symm

variable [Finite D] in
theorem a₂_not_mem_QA : a₂ ∉ pCoreOf 2 A := by
  intro h2
  have hc := (Subgroup.mem_centralizer_iff.mp (g.setup.natural.le_center g.a_mem).2 a₂ h2)
  have h3 : z * (a * a₂) = a * a₂ := by rw [← g.r20, hc]
  have h4 : z = 1 := by
    have : z * (a * a₂) = 1 * (a * a₂) := by rw [h3, one_mul]
    exact mul_right_cancel this
  exact g.setup.natural.z_ne h4

theorem u_mem_QA [Finite D] : a₁ * a₂ ∈ pCoreOf 2 A := by
  have hrel := g.setup.gold.relIndex_pCoreOf_T_left
  obtain ⟨t, htT, htQ, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have ha₁T : a₁ ∈ A ⊓ B := g.setup.QB_le_T g.a₁_mem_QB
  have ha₂T : a₂ ∈ A ⊓ B := g.setup.QB_le_T g.a₂_mem_QB
  have h1 : a₁ * t ∈ pCoreOf 2 A := (hall a₁ ha₁T).resolve_right g.a₁_not_mem_QA
  have h2 : a₂ * t ∈ pCoreOf 2 A := (hall a₂ ha₂T).resolve_right g.a₂_not_mem_QA
  have h2' : t⁻¹ * a₂ ∈ pCoreOf 2 A := by
    have := (pCoreOf 2 A).inv_mem h2
    have e : (a₂ * t)⁻¹ = t⁻¹ * a₂ := by
      calc (a₂ * t)⁻¹ = t⁻¹ * a₂⁻¹ := by group
        _ = t⁻¹ * a₂ := by rw [inv_eq_of_mul_eq_one_right g.a₂_sq]
    rwa [e] at this
  have := (pCoreOf 2 A).mul_mem h1 h2'
  have e : a₁ * t * (t⁻¹ * a₂) = a₁ * a₂ := by group
  rwa [e] at this

theorem u_mem_QB : a₁ * a₂ ∈ pCoreOf 2 B := (pCoreOf 2 B).mul_mem g.a₁_mem_QB g.a₂_mem_QB

end Gen

end GoldAmL2D

end F6

end CFSG.Quasithin
