module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraphAction
import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraphIso
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle
import CFSG.Permutation.AlternatingAutomorphism.ThreeCyclesPreserved

public section

namespace CFSG

namespace AlternatingAutomorphism

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
private theorem eq_of_forall_map_eq {σ τ : Perm α} (hα : 4 ≤ Fintype.card α)
    (h : ∀ s : Finset α, #s = 3 → s.map σ.toEmbedding = s.map τ.toEmbedding) : σ = τ := by
  classical
  ext x
  by_contra hne
  have hx : x ≠ τ.symm (σ x) := fun hx => hne ((symm_apply_eq τ).mp hx.symm)
  obtain ⟨s, hxs, hsy, hs⟩ := exists_subsuperset_card_eq (s := {x}) (n := 3)
    (t := univ.erase (τ.symm (σ x))) (by simpa using hx) (by simp)
    (by rw [card_erase_of_mem (mem_univ _), card_univ]; omega)
  have : σ x ∈ s.map τ.toEmbedding := h s hs ▸ mem_map_of_mem _ (hxs (mem_singleton_self x))
  exact (mem_erase.mp (hsy (mem_map_equiv.mp this))).1 rfl

theorem exists_perm_conj (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α)
    (f : MulAut (alternatingGroup α)) :
    ∃ σ : Perm α, ∀ g : alternatingGroup α, (f g : Perm α) = σ * g * σ⁻¹ := by
  obtain ⟨F, hF⟩ := exists_johnsonGraph_iso (isThreeCycle_map_iff hα f)
  obtain ⟨σ, hσ⟩ := johnsonGraph.exists_perm_of_iso (by omega) F
  have hsupp {c : alternatingGroup α} (hc : (c : Perm α).IsThreeCycle) :
      (f c : Perm α).support = (c : Perm α).support.map σ.toEmbedding :=
    (hF c hc).symm.trans (hσ _)
  refine ⟨σ, fun g => eq_mul_inv_iff_mul_eq.mpr (eq_of_forall_map_eq (by omega) fun s hs => ?_)⟩
  obtain ⟨c, hc, rfl⟩ := exists_alternatingGroup_isThreeCycle_support_eq hs
  have := hsupp (c := g * c * g⁻¹) (by simpa using isThreeCycle_conj hc g)
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, support_conj, hsupp hc,
    map_map] at this
  convert this using 2 <;> ext <;> simp

theorem exists_perm_conj_of_degree_eq_five_or_seven_le {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (f : MulAut (alternatingGroup (Fin n))) :
    ∃ σ : Perm (Fin n), ∀ g : alternatingGroup (Fin n),
      (f g : Perm (Fin n)) = σ * (g : Perm (Fin n)) * σ⁻¹ :=
  exists_perm_conj (by simpa using hn) f

end AlternatingAutomorphism

end CFSG
