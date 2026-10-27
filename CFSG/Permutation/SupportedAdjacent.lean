module

public import CFSG.Permutation.TranspositionCentralizer

public section

namespace CFSG.Permutation.TranspositionCentralizer

theorem fixingSubgroup_compl_eq_closure_adjacent
    {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) {k : ℕ}
    (e : Fin (k + 1) ≃ S) :
    fixingSubgroup (Equiv.Perm α) ((S : Set α)ᶜ) =
      Subgroup.closure (Set.range fun j : Fin k =>
        Equiv.swap (e j.castSucc : α) (e j.succ : α)) := by
  classical
  let f : Equiv.Perm (Fin (k + 1)) →* Equiv.Perm α :=
    (Equiv.Perm.ofSubtype (p := (· ∈ S))).comp e.permCongrHom.toMonoidHom
  have hf : ∀ j : Fin k, f (Equiv.swap j.castSucc j.succ) =
      Equiv.swap (e j.castSucc : α) (e j.succ : α) := by
    intro j
    change Equiv.Perm.ofSubtype (e.permCongr (Equiv.swap j.castSucc j.succ)) = _
    rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans, Equiv.Perm.ofSubtype_swap_eq]
  have hgen : Subgroup.closure
      (Set.range fun j : Fin k => Equiv.swap j.castSucc j.succ) = ⊤ := by
    apply top_unique
    intro σ _
    have hσ : σ ∈ Submonoid.closure
        (Set.range fun j : Fin k => Equiv.swap j.castSucc j.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    exact Submonoid.closure_le.mpr (fun x hx => Subgroup.subset_closure hx) hσ
  have hrange : f.range = (Equiv.Perm.ofSubtype (p := (· ∈ S))).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.permCongrHom.surjective,
      Subgroup.map_top]
  calc
    fixingSubgroup (Equiv.Perm α) ((S : Set α)ᶜ) = f.range :=
      (fixingSubgroup_compl_eq_range_ofSubtype (S : Set α)).trans hrange.symm
    _ = (Subgroup.closure
        (Set.range fun j : Fin k => Equiv.swap j.castSucc j.succ)).map f := by
      rw [hgen, Subgroup.map_top]
    _ = Subgroup.closure (Set.range fun j : Fin k =>
        Equiv.swap (e j.castSucc : α) (e j.succ : α)) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      funext j
      exact hf j

end CFSG.Permutation.TranspositionCentralizer

end
