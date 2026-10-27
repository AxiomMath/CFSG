module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

variable {E : Type*} [Group E]

private theorem mem_conjugate_iff_conj_mem {H : Subgroup E} {g x : E} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem centralizer_rigidity_implies_TI {M U : Subgroup E}
    (hM : normalizer (M : Set E) = M) (hUM : U ≤ M) (hUn : (U.subgroupOf M).Normal)
    (hC : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set E) ≤ M)
    (hR : ∀ u ∈ U, u ≠ 1 → ∀ g : E,
      M ⊓ centralizer ({u} : Set E) ≤ CFSG.conjugate M g → CFSG.conjugate M g = M) :
    ∀ g : E, U ⊓ CFSG.conjugate U g = ⊥ ∨ CFSG.conjugate U g = U := by
  intro g
  by_cases hI : U ⊓ CFSG.conjugate U g = ⊥
  · exact Or.inl hI
  right
  obtain ⟨⟨u, huU, hug⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  replace hug : g * u * g⁻¹ ∈ U := mem_conjugate_iff_conj_mem.mp hug
  have hv1 : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hCu : M ⊓ centralizer ({u} : Set E) ≤ CFSG.conjugate M g := by
    intro c hc'
    have hc : c * u = u * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc').2
    rw [mem_conjugate_iff_conj_mem]
    apply hC _ hug hv1
    rw [mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (g * u * g⁻¹) = g * (c * u) * g⁻¹ := by group
      _ = g * (u * c) * g⁻¹ := by rw [hc]
      _ = g * u * g⁻¹ * (g * c * g⁻¹) := by group
  have hMg := hR u huU hu1 g hCu
  have hgM : g ∈ M := by
    rw [← hM, mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff_conj_mem, hMg]
  ext x
  rw [mem_conjugate_iff_conj_mem]
  constructor
  · intro hx
    have h := hUn.conj_mem ⟨_, hUM hx⟩ hx ⟨g⁻¹, M.inv_mem hgM⟩
    rw [mem_subgroupOf] at h
    simpa [mul_assoc] using h
  · intro hx
    exact hUn.conj_mem ⟨x, hUM hx⟩ hx ⟨g, hgM⟩

end CFSG.Quasithin.SteinbergBM
