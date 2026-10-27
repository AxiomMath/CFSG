module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def invPL (l : PL) : PL := (List.range 45).map fun j => l.idxOf j

theorem repL_inv_of_comp {σ : Equiv.Perm (Fin 45)} {l m : PL} (hl : RepL l σ)
    (hm : m.length = 45) (hlt : ∀ x ∈ m, x < 45) (h : comp l m = idL) : RepL m σ⁻¹ := by
  refine ⟨hm, fun i => ?_⟩
  have hi : (i : ℕ) < m.length := by rw [hm]; exact i.2
  have hmi : m.getD i 0 < 45 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hlt _ (List.getElem_mem hi)
  have h1 : (comp l m).getD i 0 = l.getD (m.getD i 0) 0 := by
    simp only [comp, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem?_getD]
    simp [List.getElem?_eq_getElem hi]
  have h2 : (comp l m).getD i 0 = i := by
    rw [h]
    simp [idL]
  rw [h1] at h2
  have h3 := hl.2 ⟨m.getD i 0, hmi⟩
  simp only at h3
  rw [h2] at h3
  have h4 : σ ⟨m.getD i 0, hmi⟩ = i := Fin.ext h3.symm
  have : (⟨m.getD i 0, hmi⟩ : Fin 45) = σ⁻¹ i := by
    rw [Equiv.Perm.inv_def]
    exact (Equiv.eq_symm_apply σ).2 h4
  exact congrArg Fin.val this

@[expose] def spanL : List PL → List PL
  | [] => [idL]
  | g :: gs => spanL gs ++ (spanL gs).map (comp g)

theorem spanL_rep {S : Set Ah} {gens : List PL} (hS : ∀ g ∈ gens, ∃ x ∈ S, RepL g (x : P45)) :
    ∀ l ∈ spanL gens, ∃ x ∈ Subgroup.closure S, RepL l (x : P45) := by
  induction gens with
  | nil =>
    intro l hl
    have : l = idL := by simpa [spanL] using hl
    exact ⟨1, Subgroup.one_mem _, this ▸ repL_one 45⟩
  | cons g gs ih =>
    intro l hl
    have ih' := ih fun g' hg' => hS g' (List.mem_cons_of_mem g hg')
    rcases List.mem_append.1 hl with h | h
    · exact ih' l h
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
      obtain ⟨x', hx', hrep'⟩ := ih' l' hl'
      obtain ⟨xg, hxg, hrepg⟩ := hS g List.mem_cons_self
      exact ⟨xg * x', Subgroup.mul_mem _ (Subgroup.subset_closure hxg) hx', repL_mul hrepg hrep'⟩

end CFSG.Quasithin.H13.F431.U42Aut
