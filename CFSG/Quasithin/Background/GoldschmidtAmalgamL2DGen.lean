module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2D

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Gen0 (A B : Subgroup D) (z : D) (V : Subgroup D) (x a : D) : Prop where
  setup : B2Setup A B z V
  x_mem : x ∈ B
  x_cube : x * x * x = 1
  x_not : x ∉ A ⊓ B
  x2_not : x * x ∉ A ⊓ B
  a_mem : a ∈ V
  a_ne_one : a ≠ 1
  a_ne_z : a ≠ z
  V_set : (V : Set D) = {1, z, a, z * a}

theorem B2Setup.exists_gen0 [Finite D] (s : B2Setup A B z V) : ∃ x a : D, Gen0 A B z V x a := by
  obtain ⟨x, hxB, hx3⟩ := s.gold.vertex_right.exists_order_three
  obtain ⟨a, ha1, haz, hVset⟩ := s.natural.basis
  have hcube : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx3, pow_three'] at this
    exact this
  have haV : a ∈ V := by
    have : a ∈ (V : Set D) := by rw [hVset]; simp
    exact this
  exact ⟨x, a, s, hxB, hcube, s.gold.vertex_right.not_mem_of_orderOf hx3,
    s.gold.vertex_right.sq_not_mem_of_orderOf hx3, haV, ha1, haz, hVset⟩

namespace Gen0

variable {x a : D} (g : Gen0 A B z V x a)

include g

theorem mem_V_iff {v : D} : v ∈ V ↔ v = 1 ∨ v = z ∨ v = a ∨ v = z * a := by
  have := Set.ext_iff.mp g.V_set v
  simpa using this

theorem x2_mem : x * x ∈ B := B.mul_mem g.x_mem g.x_mem

theorem a_sq : a * a = 1 := g.setup.natural.mul_self_of_mem g.a_mem

theorem conj_mem_V {t v : D} (ht : t ∈ A ⊓ B) (hv : v ∈ V) : t * v * t⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (g.setup.natural.reduced.2.1 ht.1) v).mp hv

theorem conj_z : x * z * x⁻¹ = z := g.setup.central x g.x_mem

theorem conj_z' : x * x * z * (x * x)⁻¹ = z := g.setup.central (x * x) g.x2_mem

theorem V_mem_closure {v : D} (hv : v ∈ V) :
    v ∈ Subgroup.closure ({a, z, x * a * x⁻¹, x * x * a * (x * x)⁻¹} : Set D) := by
  rcases (g.mem_V_iff).mp hv with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

theorem x_conj_V {w : D} (hw : w ∈ V) :
    x * w * x⁻¹ ∈ Subgroup.closure ({a, z, x * a * x⁻¹, x * x * a * (x * x)⁻¹} : Set D) := by
  have hz := g.conj_z
  rcases (g.mem_V_iff).mp hw with rfl | rfl | rfl | rfl
  · simp
  · rw [hz]; exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · have e : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
    rw [e, hz]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

theorem xx_conj_V {w : D} (hw : w ∈ V) :
    x * x * w * (x * x)⁻¹ ∈
      Subgroup.closure ({a, z, x * a * x⁻¹, x * x * a * (x * x)⁻¹} : Set D) := by
  have hz := g.conj_z'
  rcases (g.mem_V_iff).mp hw with rfl | rfl | rfl | rfl
  · simp
  · rw [hz]; exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · have e : x * x * (z * a) * (x * x)⁻¹ =
        (x * x * z * (x * x)⁻¹) * (x * x * a * (x * x)⁻¹) := by group
    rw [e, hz]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

variable [Finite D] in
theorem conj_V_mem_closure {k : D} (hk : k ∈ B) {v : D} (hv : v ∈ V) :
    k * v * k⁻¹ ∈ Subgroup.closure ({a, z, x * a * x⁻¹, x * x * a * (x * x)⁻¹} : Set D) := by
  rcases coset_decomp g.setup.gold.relIndex_right g.x_mem g.x_not g.x2_not hk with
    hkT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · exact g.V_mem_closure (g.conj_mem_V hkT hv)
  · have e : x * t * v * (x * t)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
    rw [e]; exact g.x_conj_V (g.conj_mem_V htT hv)
  · have e : x * x * t * v * (x * x * t)⁻¹ = x * x * (t * v * t⁻¹) * (x * x)⁻¹ := by group
    rw [e]; exact g.xx_conj_V (g.conj_mem_V htT hv)

omit g in
theorem pairwise_comm_gens {x a a₁ a₂ : D} (e1 : x * a * x⁻¹ = a₁) (e2 : x * a₁ * x⁻¹ = a₂)
    (e3 : x * a₂ * x⁻¹ = a) (h01 : a * a₁ = a₁ * a) (hz0 : z * a = a * z)
    (hz1 : z * a₁ = a₁ * z) (hz2 : z * a₂ = a₂ * z) :
    ∀ p ∈ ({a, z, a₁, a₂} : Set D), ∀ q ∈ ({a, z, a₁, a₂} : Set D), p * q = q * p := by
  have c01 : x * (a * a₁) * x⁻¹ = a₁ * a₂ := by
    calc x * (a * a₁) * x⁻¹ = (x * a * x⁻¹) * (x * a₁ * x⁻¹) := by group
      _ = a₁ * a₂ := by rw [e1, e2]
  have c10 : x * (a₁ * a) * x⁻¹ = a₂ * a₁ := by
    calc x * (a₁ * a) * x⁻¹ = (x * a₁ * x⁻¹) * (x * a * x⁻¹) := by group
      _ = a₂ * a₁ := by rw [e1, e2]
  have h12 : a₁ * a₂ = a₂ * a₁ := by rw [← c01, ← c10, h01]
  have c12 : x * (a₁ * a₂) * x⁻¹ = a₂ * a := by
    calc x * (a₁ * a₂) * x⁻¹ = (x * a₁ * x⁻¹) * (x * a₂ * x⁻¹) := by group
      _ = a₂ * a := by rw [e2, e3]
  have c21 : x * (a₂ * a₁) * x⁻¹ = a * a₂ := by
    calc x * (a₂ * a₁) * x⁻¹ = (x * a₂ * x⁻¹) * (x * a₁ * x⁻¹) := by group
      _ = a * a₂ := by rw [e2, e3]
  have h20 : a₂ * a = a * a₂ := by rw [← c12, ← c21, h12]
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq <;> rw [hp, hq] <;>
    first
    | rfl
    | exact h01
    | exact h01.symm
    | exact h12
    | exact h12.symm
    | exact h20
    | exact h20.symm
    | exact hz0
    | exact hz0.symm
    | exact hz1
    | exact hz1.symm
    | exact hz2
    | exact hz2.symm

variable [Finite D] in
theorem not_comm : a * (x * a * x⁻¹) ≠ (x * a * x⁻¹) * a := by
  intro hcomm
  obtain ⟨x₀, hx₀B, hne⟩ := g.setup.nc
  apply hne
  have haB : a ∈ B := pCoreOf_le 2 B (g.setup.V_le g.a_mem)
  have ha₁B : x * a * x⁻¹ ∈ B := B.mul_mem (B.mul_mem g.x_mem haB) (B.inv_mem g.x_mem)
  have ha₂B : x * x * a * (x * x)⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem g.x2_mem haB) (B.inv_mem g.x2_mem)
  have e1 : x * a * x⁻¹ = x * a * x⁻¹ := rfl
  have e2 : x * (x * a * x⁻¹) * x⁻¹ = x * x * a * (x * x)⁻¹ := by group
  have e3 : x * (x * x * a * (x * x)⁻¹) * x⁻¹ = a := by
    calc x * (x * x * a * (x * x)⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
      _ = a := by rw [g.x_cube]; group
  have hS := pairwise_comm_gens (z := z) e1 e2 e3 hcomm (g.setup.z_comm haB).symm
    (g.setup.z_comm ha₁B).symm (g.setup.z_comm ha₂B).symm
  refine eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_)
  rw [Subgroup.mem_bot]
  have hv₂ : x₀⁻¹ * g₂ * x₀ ∈ V := mem_conjSub.mp hg₂
  have hg₂' : x₀ * (x₀⁻¹ * g₂ * x₀) * x₀⁻¹ = g₂ := by group
  have hcl₂ := g.conj_V_mem_closure hx₀B hv₂
  rw [hg₂'] at hcl₂
  have hcl₁ : g₁ ∈ Subgroup.closure ({a, z, x * a * x⁻¹, x * x * a * (x * x)⁻¹} : Set D) := by
    have := g.conj_V_mem_closure B.one_mem hg₁
    simpa using this
  exact commutatorElement_eq_one_iff_mul_comm.mpr (B2Setup.closure_comm hS hcl₁ hcl₂)

end Gen0

end GoldAmL2D

end F6

end CFSG.Quasithin
