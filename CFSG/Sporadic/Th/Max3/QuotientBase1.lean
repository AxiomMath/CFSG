
module


public import CFSG.Sporadic.Th.Max3.RelationsBase1

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

namespace AltQuot

theorem nfN_mem_Q (s : ℕ) (e : Fin 8 → ℕ) : nfN s e ∈ Q :=
  Q.mul_mem (Subgroup.pow_mem _ z_mem_Q _)
    (Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact Subgroup.pow_mem _ (q_mem_Q i) _)

theorem nfAt_mem_Q (k : Fin 512) : nfAt k ∈ Q := nfN_mem_Q _ _

end AltQuot

namespace AltQuot

abbrev MQ : Type := ↥M ⧸ Q.subgroupOf M

@[expose] noncomputable def proj [(CFSG.Sporadic.Th.Max3.Q.subgroupOf CFSG.Sporadic.Th.Max3.M).Normal] :
    ↥M →* MQ := QuotientGroup.mk' (Q.subgroupOf M)

theorem proj_surjective [(CFSG.Sporadic.Th.Max3.Q.subgroupOf CFSG.Sporadic.Th.Max3.M).Normal] :
    Function.Surjective proj := QuotientGroup.mk'_surjective _

theorem proj_eq_one_iff [(CFSG.Sporadic.Th.Max3.Q.subgroupOf CFSG.Sporadic.Th.Max3.M).Normal]
    {g : ↥M} : proj g = 1 ↔ (g : J) ∈ Q := QuotientGroup.eq_one_iff g

theorem proj_eq_proj_iff [(CFSG.Sporadic.Th.Max3.Q.subgroupOf CFSG.Sporadic.Th.Max3.M).Normal]
    {g h : ↥M} : proj g = proj h ↔ (g : J)⁻¹ * h ∈ Q := QuotientGroup.eq

theorem proj_mem_of_generators [(CFSG.Sporadic.Th.Max3.Q.subgroupOf CFSG.Sporadic.Th.Max3.M).Normal]
    {H : Subgroup MQ} (hx : proj ⟨x, x_mem_M⟩ ∈ H)
    (hy : proj ⟨y, y_mem_M⟩ ∈ H) (g : J) (hg : g ∈ M) : proj ⟨g, hg⟩ ∈ H := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact hx
    · exact hy
  | one =>
    have e : proj ⟨1, M.one_mem⟩ = 1 := map_one proj
    rw [e]
    exact H.one_mem
  | mul g h hg hh ihg ihh =>
    have e : proj ⟨g * h, M.mul_mem hg hh⟩ = proj ⟨g, hg⟩ * proj ⟨h, hh⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact H.mul_mem ihg ihh
  | inv g hg ih =>
    have e : proj ⟨g⁻¹, M.inv_mem hg⟩ = (proj ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact H.inv_mem ih

end AltQuot

open AltQuot

namespace AltQuot

end AltQuot

end CFSG.Sporadic.Th.Max3
