module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Check
public import CFSG.Sporadic.Mathieu.Simple

public section

namespace CFSG.Quasithin.Asc94

open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239
open scoped Pointwise

abbrev heptad₀ : Finset (Fin 23) := M23Insp.data.B₀

theorem m23Insp_hgens : Subgroup.closure {g | g ∈ M23Insp.data.gens} = ⊤ := by
  have h := Sporadic.Mathieu.closure_pair_eq_top Sporadic.Schreier.m23_eq_closure
    Sporadic.Schreier.m23GenA.2 Sporadic.Schreier.m23GenB.2
  have hg : M23Insp.data.gens = [Sporadic.Schreier.m23GenA, Sporadic.Schreier.m23GenB] := rfl
  have : {g | g ∈ M23Insp.data.gens} =
      ({Sporadic.Schreier.m23GenA, Sporadic.Schreier.m23GenB} : Set ↥NativeSporadic.M23) := by
    rw [hg]
    ext g
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  rw [this]
  exact h

theorem smul_heptad₀_mem
    (g : ↥NativeSporadic.M23) : g • heptad₀ ∈ M23Insp.data.H :=
  (orbit_eq_of_reach_closed m23Insp_hgens M23Insp.chk_H_reach M23Insp.chk_H_closed _).1 ⟨g, rfl⟩

theorem card_inter_heptad₀_le
    {B : Finset (Fin 23)} (hB : B ∈ M23Insp.data.H)
    (hne : B ≠ heptad₀) : (B ∩ heptad₀).card ≤ 3 := by
  rcases M23Insp.chk_cover B hB hne with h | h
  · rw [(M23Insp.chk_lev₁ B hB hne).mp h]; decide
  · rw [(M23Insp.chk_lev₂ B hB hne).mp h]; decide

theorem smul_heptad₀_of_smul_quad
    {Q : Finset (Fin 23)} (hQ : Q ⊆ heptad₀) (hcard : Q.card = 4)
    {g : ↥NativeSporadic.M23} (hg : g • Q = Q) : g • heptad₀ = heptad₀ := by
  by_contra hne
  have h3 := card_inter_heptad₀_le (smul_heptad₀_mem g) hne
  have hsub : Q ⊆ g • heptad₀ ∩ heptad₀ := by
    intro x hx
    refine Finset.mem_inter.mpr ⟨?_, hQ hx⟩
    rw [← hg] at hx
    exact Finset.smul_finset_subset_smul_finset hQ hx
  have := Finset.card_le_card hsub
  omega

end CFSG.Quasithin.Asc94
