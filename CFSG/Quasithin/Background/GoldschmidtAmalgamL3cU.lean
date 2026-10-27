module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cGen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Card

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem mem_normalizer_of_cube {W : Subgroup D} {y : D} (hy : y * y * y = 1)
    (h : ∀ w ∈ W, y * w * y⁻¹ ∈ W) : y ∈ Subgroup.normalizer (W : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h w, fun hw => ?_⟩
  have h2 := h _ hw
  have h3 := h _ h2
  have e : y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = w := by
    calc y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * w * (y * y * y)⁻¹ := by group
      _ = w := by rw [hy]; group
  rwa [e] at h3

section U

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

omit [Finite D] in
theorem Gen3.T_le_normalizer_V : A ⊓ B ≤ Subgroup.normalizer (V : Set D) :=
  inf_le_left.trans g.hyp.natural.reduced.2.1

theorem Gen3.x_not_mem_normalizer_V : x ∉ Subgroup.normalizer (V : Set D) := by
  intro hx
  obtain ⟨b, hb, hbN⟩ := g.hyp.exists_not_mem_normalizer
  apply hbN
  rcases coset_decomp g.hyp.gold.relIndex_right g.x_mem g.x_not g.x2_not hb with hbT |
      ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · exact g.T_le_normalizer_V hbT
  · exact Subgroup.mul_mem _ hx (g.T_le_normalizer_V htT)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hx) (g.T_le_normalizer_V htT)

theorem Gen3.a₁_not_mem_V : a₁ ∉ V := by
  intro ha₁
  apply g.x_not_mem_normalizer_V
  refine mem_normalizer_of_cube g.x_cube fun v hv => ?_
  rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
  · simp
  · rw [g.conj_z]; exact g.hyp.natural.z_mem_V
  · rw [g.conj_a]; exact ha₁
  · have e : x * (z * a) * x⁻¹ = z * a₁ := by
      calc x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
        _ = z * a₁ := by rw [g.conj_z, g.conj_a]
    rw [e]
    exact V.mul_mem g.hyp.natural.z_mem_V ha₁

theorem Gen3.a₂_not_mem_V : a₂ ∉ V := by
  intro ha₂
  have hxx : (x * x) * (x * x) * (x * x) = 1 := by
    calc (x * x) * (x * x) * (x * x) = (x * x * x) * (x * x * x) := by group
      _ = 1 := by rw [g.x_cube]; group
  have hn : x * x ∈ Subgroup.normalizer (V : Set D) := by
    refine mem_normalizer_of_cube hxx fun v hv => ?_
    rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
    · simp
    · rw [g.hyp.central (x * x) g.x2_mem]; exact g.hyp.natural.z_mem_V
    · rw [← g.a₂_eq]; exact ha₂
    · have e : x * x * (z * a) * (x * x)⁻¹ = z * a₂ := by
        calc x * x * (z * a) * (x * x)⁻¹
            = (x * x * z * (x * x)⁻¹) * (x * x * a * (x * x)⁻¹) := by group
          _ = z * a₂ := by rw [g.hyp.central (x * x) g.x2_mem, ← g.a₂_eq]
      rw [e]
      exact V.mul_mem g.hyp.natural.z_mem_V ha₂
  apply g.x_not_mem_normalizer_V
  have e : x = (x * x) * (x * x) := by
    calc x = x * (x * x * x) := by rw [g.x_cube, mul_one]
      _ = (x * x) * (x * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ hn hn

omit [Finite D] in
theorem Gen3.relIndex_V_U (hU : Nat.card (conjClosure V B) = 8) :
    V.relIndex (conjClosure V B) = 2 := by
  have h1 := Subgroup.relIndex_mul_card V (conjClosure V B)
  rw [inf_eq_left.mpr (le_conjClosure V B), g.hyp.natural.card_eq, hU] at h1
  omega

omit [Finite D] in
theorem Gen3.mul_inv_mem_V_of_not_mem (hU : Nat.card (conjClosure V B) = 8) {u w : D}
    (hu : u ∈ conjClosure V B) (hw : w ∈ conjClosure V B) (huV : u ∉ V) (hwV : w ∉ V) :
    u * w⁻¹ ∈ V := by
  obtain ⟨c, -, hc⟩ := Subgroup.relIndex_eq_two_iff.mp (g.relIndex_V_U hU)
  have huc : u * c ∈ V := by
    rcases hc u hu with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 huV
  have hwc : w * c ∈ V := by
    rcases hc w hw with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hwV
  have e : u * w⁻¹ = (u * c) * (w * c)⁻¹ := by group
  rw [e]
  exact V.mul_mem huc (V.inv_mem hwc)

theorem Gen3.a₂_eq_or (hU : Nat.card (conjClosure V B) = 8) :
    a₂ = a * a₁ ∨ a₂ = z * a * a₁ := by
  have hmem := g.mul_inv_mem_V_of_not_mem hU g.a₂_mem_U g.a₁_mem_U g.a₂_not_mem_V
    g.a₁_not_mem_V
  have ha₁inv : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right g.a₁_sq
  rw [ha₁inv] at hmem
  have hca : x * a₂ * x⁻¹ = a := g.conj_a₂
  rcases g.mem_V_iff.mp hmem with e | e | e | e
  · exfalso
    have h1 : a₂ = a₁ := by
      calc a₂ = (a₂ * a₁) * a₁⁻¹ := by group
        _ = a₁ := by rw [e, one_mul, ha₁inv]
    apply g.a₁_not_mem_V
    have h2 : a = a₁ := by rw [← hca, h1, g.conj_a₁, h1]
    rw [← h2]; exact g.a_mem
  · exfalso
    have h1 : a₂ = z * a₁ := by
      calc a₂ = (a₂ * a₁) * a₁⁻¹ := by group
        _ = z * a₁ := by rw [ha₁inv, e]
    apply g.a₁_not_mem_V
    have h2 : a = a₁ := by
      calc a = x * a₂ * x⁻¹ := hca.symm
        _ = (x * z * x⁻¹) * (x * a₁ * x⁻¹) := by rw [h1]; group
        _ = z * a₂ := by rw [g.conj_z, g.conj_a₁]
        _ = z * (z * a₁) := by rw [h1]
        _ = a₁ := by rw [← mul_assoc, g.z_mul_z, one_mul]
    rw [← h2]; exact g.a_mem
  · left
    calc a₂ = (a₂ * a₁) * a₁⁻¹ := by group
      _ = a * a₁ := by rw [ha₁inv, e]
  · right
    calc a₂ = (a₂ * a₁) * a₁⁻¹ := by group
      _ = z * a * a₁ := by rw [ha₁inv, e]

end U

end GoldAmL3c

end F6

end CFSG.Quasithin
