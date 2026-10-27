module

public import CFSG.Quasithin.Background.RonanE114SevenL35Defs

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups
open CFSG.Wreathed CFSG.Wreathed.BrauerWong

theorem modelBase_eq35 :
    (modelBase sylowS35 e35 : Subgroup SL(3, ZMod 5)) = Subgroup.closure {u35, v35} :=
  wg35.modelBase_eq (by norm_num)

theorem modelV_eq35 :
    (modelV sylowS35 e35 : Subgroup SL(3, ZMod 5)) =
      Subgroup.closure {u35 * v35, u35 ^ 2, s35} := by
  have ha : wreathModelHom sylowS35 e35 (Original.a (2 ^ 2)) = u35 * v35 :=
    wg35.modelHom_a (by norm_num)
  have hx2 : wreathModelHom sylowS35 e35 (Original.x2 (2 ^ 2)) = u35 ^ 2 :=
    wg35.modelHom_x2 (by norm_num)
  have hz : wreathModelHom sylowS35 e35 (Original.z (2 ^ 2)) = s35 :=
    wg35.modelHom_z (by norm_num)
  rw [modelV, Original.V, MonoidHom.map_closure, Set.image_insert_eq, Set.image_pair, ha, hx2, hz]

theorem conj_mem_closure_L35 {G : Type*} [Group G] (S : Set G) (g : G)
    (h : ∀ y ∈ S, g * y * g⁻¹ ∈ Subgroup.closure S) {x : G} (hx : x ∈ Subgroup.closure S) :
    g * x * g⁻¹ ∈ Subgroup.closure S := by
  have hle : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  exact hle (Subgroup.mem_map_of_mem _ hx)

theorem p23_conj_u35 : p23 * u35 * p23⁻¹ = u35 * v35⁻¹ := by decide

theorem p23_conj_v35 : p23 * v35 * p23⁻¹ = v35⁻¹ := by decide

theorem c3_conj_u35 : c3 * u35 * c3⁻¹ = v35 * u35⁻¹ := by decide

theorem c3_conj_v35 : c3 * v35 * c3⁻¹ = u35⁻¹ := by decide

theorem x1_conj_uv35 : x1 * (u35 * v35) * x1⁻¹ = u35 * v35 := by decide

theorem x1_conj_u2_35 : x1 * u35 ^ 2 * x1⁻¹ = s35⁻¹ * (u35 * v35)⁻¹ * (u35 ^ 2)⁻¹ := by
  decide

theorem x1_conj_s35 : x1 * s35 * x1⁻¹ = (u35 ^ 2)⁻¹ := by decide

theorem p23_mem_normalizer35 :
    p23 ∈ Subgroup.normalizer
      ((modelBase sylowS35 e35 : Subgroup SL(3, ZMod 5)) : Set SL(3, ZMod 5)) := by
  apply mem_normalizer_of_forall_conj_mem
  intro x hx
  rw [modelBase_eq35] at hx ⊢
  refine conj_mem_closure_L35 ({u35, v35} : Set SL(3, ZMod 5)) p23 ?_ hx
  rintro y (rfl | rfl)
  · rw [p23_conj_u35]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  · rw [p23_conj_v35]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem c3_mem_normalizer35 :
    c3 ∈ Subgroup.normalizer
      ((modelBase sylowS35 e35 : Subgroup SL(3, ZMod 5)) : Set SL(3, ZMod 5)) := by
  apply mem_normalizer_of_forall_conj_mem
  intro x hx
  rw [modelBase_eq35] at hx ⊢
  refine conj_mem_closure_L35 ({u35, v35} : Set SL(3, ZMod 5)) c3 ?_ hx
  rintro y (rfl | rfl)
  · rw [c3_conj_u35]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  · rw [c3_conj_v35]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem x1_mem_normalizer35 :
    x1 ∈ Subgroup.normalizer
      ((modelV sylowS35 e35 : Subgroup SL(3, ZMod 5)) : Set SL(3, ZMod 5)) := by
  apply mem_normalizer_of_forall_conj_mem
  intro x hx
  rw [modelV_eq35] at hx ⊢
  refine conj_mem_closure_L35 ({u35 * v35, u35 ^ 2, s35} : Set SL(3, ZMod 5)) x1 ?_ hx
  rintro y (rfl | rfl | rfl)
  · rw [x1_conj_uv35]
    exact Subgroup.subset_closure (by simp)
  · rw [x1_conj_u2_35]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  · rw [x1_conj_s35]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

end CFSG.Quasithin.RonanE114.Seven.L35
