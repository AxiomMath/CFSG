module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ASVolI.ChH

open Subgroup Pointwise

theorem exists_mem_map_conj_le_of_card_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K P E : Subgroup G} (hPK : P ≤ K) (hEK : E ≤ K)
    (hP : Nat.card P = p ^ (Nat.card K).factorization p) (hE : IsPGroup p E) :
    ∃ g ∈ K, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  have hcard : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv).trans hP
  let S : Sylow p K := Sylow.ofCard (P.subgroupOf K) hcard
  have hE' : IsPGroup p (E.subgroupOf K) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S Q
  refine ⟨((g⁻¹ : K) : G), (g⁻¹).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : (⟨x, hEK hx⟩ : K) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hx)
  rw [← hg] at h1
  have h2 : (⟨x, hEK hx⟩ : K) ∈ ((g • S : Sylow p K) : Subgroup K) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : ((MulAut.conj g)⁻¹ • (⟨x, hEK hx⟩ : K) : K) ∈ P.subgroupOf K := h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa [MulAut.smul_def, ← map_inv] using h3

end CFSG.ASVolI.ChH
