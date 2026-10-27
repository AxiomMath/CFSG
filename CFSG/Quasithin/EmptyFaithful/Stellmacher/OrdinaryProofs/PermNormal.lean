module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open Equiv

theorem normal_subgroupOf_of_normal {G : Type} [Group G] {H : Subgroup G}
    (hH : H.Normal) (K : Subgroup G) : (H.subgroupOf K).Normal :=
  ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (by
    simpa using hH.conj_mem _ (Subgroup.mem_subgroupOf.mp hn) (g : G))⟩

def cyc012 : Perm (Fin 5) := swap 0 1 * swap 1 2

def cyc013 : Perm (Fin 5) := swap 0 1 * swap 1 3

set_option maxRecDepth 8000 in
theorem centralizer_cyc_trivial :
    ∀ σ : Perm (Fin 5), σ * cyc012 = cyc012 * σ → σ * cyc013 = cyc013 * σ → σ = 1 := by
  decide

theorem cyc012_mem : cyc012 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc012, Perm.sign_mul,
    Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
    Perm.sign_swap (show (1 : Fin 5) ≠ 2 by decide)]
  rfl

theorem cyc013_mem : cyc013 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc013, Perm.sign_mul,
    Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
    Perm.sign_swap (show (1 : Fin 5) ≠ 3 by decide)]
  rfl

theorem normal_perm_five (N : Subgroup (Perm (Fin 5))) (hN : N.Normal) :
    N = ⊥ ∨ N = alternatingGroup (Fin 5) ∨ N = ⊤ := by
  have hAn : (alternatingGroup (Fin 5)).Normal := inferInstance
  have hNA : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    normal_subgroupOf_of_normal hN _
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp)
    (N := N.subgroupOf (alternatingGroup (Fin 5))) with h | h
  · have hMbot : N ⊓ alternatingGroup (Fin 5) = ⊥ :=
      disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
    by_cases hle : N ≤ alternatingGroup (Fin 5)
    · left
      rwa [inf_eq_left.mpr hle] at hMbot
    · exfalso
      obtain ⟨σ, hσN, hσA⟩ := IsConcreteLE.not_le_iff_exists.mp hle
      have hcomm : ∀ a ∈ alternatingGroup (Fin 5), σ * a = a * σ := by
        intro a ha
        have hk1 : σ * a * σ⁻¹ * a⁻¹ ∈ N := by
          have e : σ * a * σ⁻¹ * a⁻¹ = σ * (a * σ⁻¹ * a⁻¹) := by
            simp only [mul_assoc]
          rw [e]
          exact N.mul_mem hσN (hN.conj_mem σ⁻¹ (N.inv_mem hσN) a)
        have hk2 : σ * a * σ⁻¹ * a⁻¹ ∈ alternatingGroup (Fin 5) :=
          (alternatingGroup (Fin 5)).mul_mem (hAn.conj_mem a ha σ)
            ((alternatingGroup (Fin 5)).inv_mem ha)
        have hk : σ * a * σ⁻¹ * a⁻¹ = 1 := by
          have hmem : σ * a * σ⁻¹ * a⁻¹ ∈ N ⊓ alternatingGroup (Fin 5) :=
            Subgroup.mem_inf.mpr ⟨hk1, hk2⟩
          rw [hMbot] at hmem
          exact Subgroup.mem_bot.mp hmem
        have hconj : σ * a * σ⁻¹ = a := mul_inv_eq_one.mp hk
        calc σ * a = σ * a * σ⁻¹ * σ := by group
          _ = a * σ := by rw [hconj]
      have h1 : σ * cyc012 = cyc012 * σ := hcomm cyc012 cyc012_mem
      have h2 : σ * cyc013 = cyc013 * σ := hcomm cyc013 cyc013_mem
      have hσ1 : σ = 1 := centralizer_cyc_trivial σ h1 h2
      exact hσA (by rw [hσ1]; exact (alternatingGroup (Fin 5)).one_mem)
  · have hAN : alternatingGroup (Fin 5) ≤ N := Subgroup.subgroupOf_eq_top.mp h
    by_cases hle : N ≤ alternatingGroup (Fin 5)
    · right; left
      exact le_antisymm hle hAN
    · right; right
      obtain ⟨σ, hσN, hσA⟩ := IsConcreteLE.not_le_iff_exists.mp hle
      have hσs : Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σ) with e | e
        · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr e) hσA
        · exact e
      rw [eq_top_iff]
      intro g _
      by_cases hgA : g ∈ alternatingGroup (Fin 5)
      · exact hAN hgA
      · have hgs : Perm.sign g = -1 := by
          rcases Int.units_eq_one_or (Perm.sign g) with e | e
          · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr e) hgA
          · exact e
        have hgσA : g * σ ∈ alternatingGroup (Fin 5) :=
          Equiv.Perm.mem_alternatingGroup.mpr (by rw [Perm.sign_mul, hgs, hσs]; rfl)
        have hgσN : g * σ ∈ N := hAN hgσA
        have hmem : g * σ * σ⁻¹ ∈ N := N.mul_mem hgσN (N.inv_mem hσN)
        simpa using hmem

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
