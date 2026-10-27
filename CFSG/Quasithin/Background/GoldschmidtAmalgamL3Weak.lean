module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Card

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem exists_conj_eq_of_mem (h : GoldHyp A B) (hn : IsNaturalAt A (A ⊓ B) z V) {c : D}
    (hcV : c ∈ V) (hc1 : c ≠ 1) : ∃ a ∈ A, a * z * a⁻¹ = c := by
  obtain ⟨x, hxA, hx3⟩ := h.vertex_left.exists_order_three
  obtain ⟨a₀, ha1, haz, hVset⟩ := hn.basis
  have hxT : x ∉ A ⊓ B := h.vertex_left.not_mem_of_orderOf hx3
  have hx2T : x * x ∉ A ⊓ B := h.vertex_left.sq_not_mem_of_orderOf hx3
  have hxxA : x * x ∈ A := A.mul_mem hxA hxA
  have hzV : z ∈ V := hn.z_mem_V
  have hne : ∀ w ∈ A, w ∉ A ⊓ B → w * z * w⁻¹ ≠ z := by
    intro w hwA hwT e
    exact hwT (inf_normalizer_zpowers_le h hn
      ⟨hwA, mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq e)⟩)
  have e1 : x * z * x⁻¹ ≠ z := hne x hxA hxT
  have e2 : x * x * z * (x * x)⁻¹ ≠ z := hne (x * x) hxxA hx2T
  have e12 : x * z * x⁻¹ ≠ x * x * z * (x * x)⁻¹ := by
    intro e
    have h' : x⁻¹ * (x * z * x⁻¹) * x = x⁻¹ * (x * x * z * (x * x)⁻¹) * x := by rw [e]
    have l : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    have r : x⁻¹ * (x * x * z * (x * x)⁻¹) * x = x * z * x⁻¹ := by group
    rw [l, r] at h'
    exact e1 h'.symm
  have hV1 : x * z * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hn.reduced.2.1 hxA) z).mp hzV
  have hV2 : x * x * z * (x * x)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hn.reduced.2.1 hxxA) z).mp hzV
  have hn1 : x * z * x⁻¹ ≠ 1 := fun e => hn.z_ne (conj_eq_one_iff.mp e)
  have hn2 : x * x * z * (x * x)⁻¹ ≠ 1 := fun e => hn.z_ne (conj_eq_one_iff.mp e)
  have hmemV : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = a₀ ∨ v = z * a₀ := by
    intro v hv
    have : v ∈ (V : Set D) := hv
    rw [hVset] at this
    simpa using this
  have hα : x * z * x⁻¹ = a₀ ∨ x * z * x⁻¹ = z * a₀ := by
    rcases hmemV _ hV1 with e | e | e | e
    · exact absurd e hn1
    · exact absurd e e1
    · exact Or.inl e
    · exact Or.inr e
  have hβ : x * x * z * (x * x)⁻¹ = a₀ ∨ x * x * z * (x * x)⁻¹ = z * a₀ := by
    rcases hmemV _ hV2 with e | e | e | e
    · exact absurd e hn2
    · exact absurd e e2
    · exact Or.inl e
    · exact Or.inr e
  rcases hmemV c hcV with e | e | e | e
  · exact absurd e hc1
  · exact ⟨1, A.one_mem, by simp [e]⟩
  · rcases hα with hα | hα
    · exact ⟨x, hxA, hα.trans e.symm⟩
    · rcases hβ with hβ | hβ
      · exact ⟨x * x, hxxA, hβ.trans e.symm⟩
      · exact absurd (hα.trans hβ.symm) e12
  · rcases hα with hα | hα
    · rcases hβ with hβ | hβ
      · exact absurd (hα.trans hβ.symm) e12
      · exact ⟨x * x, hxxA, hβ.trans e.symm⟩
    · exact ⟨x, hxA, hα.trans e.symm⟩

end GoldAmL3

end F6

end CFSG.Quasithin
