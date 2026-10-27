module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

theorem exists_Φ1_of_mem_conj {g : G} {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hu : g * C.z * g⁻¹ ∈ W) {x : G} (hx : g * x * g⁻¹ ∈ W) : ∃ y ∈ P1, C.Φ1 y = x := by
  have h := hWab _ hx _ hu
  have h2 : x * C.z = C.z * x := by
    have : g * (x * C.z) * g⁻¹ = g * (C.z * x) * g⁻¹ := by
      calc g * (x * C.z) * g⁻¹ = (g * x * g⁻¹) * (g * C.z * g⁻¹) := by group
        _ = (g * C.z * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (C.z * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  exact C.exists_of_comm_z h2

theorem pre1_props {g : G} {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hWsq : ∀ x ∈ W, x * x = 1) (hu : g * C.z * g⁻¹ ∈ W) :
    (∀ a ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom),
      ∀ b ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom), a * b = b * a) ∧
    (∀ a ∈ C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom), a * a = 1) ∧
    Nat.card (C.pre1 (W.map (MulAut.conj g⁻¹).toMonoidHom)) = Nat.card W := by
  have hmem : ∀ x, x ∈ W.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ W := by
    intro x
    rw [mem_map_conj]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨haP, haA⟩ := C.mem_pre1.1 ha
    obtain ⟨hbP, hbA⟩ := C.mem_pre1.1 hb
    have h1 := hWab _ ((hmem _).1 haA) _ ((hmem _).1 hbA)
    have h2 : C.Φ1 a * C.Φ1 b = C.Φ1 b * C.Φ1 a := by
      have : g * (C.Φ1 a * C.Φ1 b) * g⁻¹ = g * (C.Φ1 b * C.Φ1 a) * g⁻¹ := by
        calc g * (C.Φ1 a * C.Φ1 b) * g⁻¹ = (g * C.Φ1 a * g⁻¹) * (g * C.Φ1 b * g⁻¹) := by group
          _ = (g * C.Φ1 b * g⁻¹) * (g * C.Φ1 a * g⁻¹) := h1
          _ = g * (C.Φ1 b * C.Φ1 a) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
    rw [← C.Φ1_mul haP hbP, ← C.Φ1_mul hbP haP] at h2
    exact C.Φ1_inj (P1.mul_mem haP hbP) (P1.mul_mem hbP haP) h2
  · intro a ha
    obtain ⟨haP, haA⟩ := C.mem_pre1.1 ha
    have h1 := hWsq _ ((hmem _).1 haA)
    have h2 : C.Φ1 a * C.Φ1 a = 1 := by
      have : g * (C.Φ1 a * C.Φ1 a) * g⁻¹ = 1 := by
        calc g * (C.Φ1 a * C.Φ1 a) * g⁻¹ = (g * C.Φ1 a * g⁻¹) * (g * C.Φ1 a * g⁻¹) := by group
          _ = 1 := h1
      simpa using this
    rw [← C.Φ1_mul haP haP, ← C.Φ1_one] at h2
    exact C.Φ1_inj (P1.mul_mem haP haP) P1.one_mem h2
  · have hle : W.map (MulAut.conj g⁻¹).toMonoidHom ≤ C.φ1.range := by
      intro x hx
      obtain ⟨y, hyP, rfl⟩ := C.exists_Φ1_of_mem_conj hWab hu ((hmem x).1 hx)
      exact ⟨⟨y, hyP⟩, (C.Φ1_of_mem hyP).symm⟩
    rw [C.card_pre1 hle, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

end Ctx

end CFSG.Quasithin.H13.F431.U42
