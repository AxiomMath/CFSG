module

public import Mathlib.GroupTheory.IsPerfect

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

theorem pCore_prod_eq_bot {A B : Type} [Group A] [Group B] (hA : CFSG.pCore 2 A = ⊥)
    (hB : CFSG.pCore 2 B = ⊥) : CFSG.pCore 2 (A × B) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hfs : Function.Surjective (MonoidHom.fst A B) := fun a => ⟨(a, 1), rfl⟩
  have hss : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  have h1 : (CFSG.pCore 2 (A × B)).map (MonoidHom.fst A B) ≤ CFSG.pCore 2 A :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ hfs, CFSG.pCore_isPGroup.map _⟩
  have h2 : (CFSG.pCore 2 (A × B)).map (MonoidHom.snd A B) ≤ CFSG.pCore 2 B :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ hss, CFSG.pCore_isPGroup.map _⟩
  rw [hA] at h1
  rw [hB] at h2
  have e1 : x.1 = 1 := by
    have : x.1 ∈ (CFSG.pCore 2 (A × B)).map (MonoidHom.fst A B) := ⟨x, hx, rfl⟩
    simpa using h1 this
  have e2 : x.2 = 1 := by
    have : x.2 ∈ (CFSG.pCore 2 (A × B)).map (MonoidHom.snd A B) := ⟨x, hx, rfl⟩
    simpa using h2 this
  exact Prod.ext e1 e2

theorem isPerfect_prod {A B : Type} [Group A] [Group B] (hA : Group.IsPerfect A)
    (hB : Group.IsPerfect B) : Group.IsPerfect (A × B) := by
  rw [Group.isPerfect_def, _root_.commutator_def, ← Subgroup.top_prod_top,
    Subgroup.commutator_prod_prod, ← _root_.commutator_def, ← _root_.commutator_def,
    hA.commutator_eq_top, hB.commutator_eq_top, Subgroup.top_prod_top]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
