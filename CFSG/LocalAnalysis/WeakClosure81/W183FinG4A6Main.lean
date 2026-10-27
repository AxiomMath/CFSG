module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6Par
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6E8
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6Moves

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

theorem w183finG4A6_autNoDynkin_eq
    {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6)) :
    autNoDynkin M = w183finG4A6AutS6 e := by
  have hset : {φ : MulAut M | ¬ ActsOnDynkinMod ⊥ (innAutOf M) φ} =
      (w183finG4A6AutS6 e : Set (MulAut M)) := by
    ext γ
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hγ
      exact h (w183finG4A6_acts_of_not_mem_autS6 e γ hγ)
    · intro h hacts
      exact w183finG4A6_not_mem_autS6_of_acts e γ hacts h
  unfold autNoDynkin
  rw [hset]
  exact Subgroup.closure_eq _

theorem finG4A6_holds : FinG4A6 := by
  intro M _ hM
  obtain ⟨e⟩ := hM
  rw [w183finG4A6_autNoDynkin_eq e]
  exact ⟨w183finG4A6_autS6_normal e, w183finG4A6_elemAbelian_le_autS6 e,
    w183finG4A6_inn_sup_eq_autS6 e, w183finG4A6_br2NormalConj_autS6 e,
    w183finG4A6_br2DynkinMoves_autS6 e⟩

end CFSG.LocalAnalysis.WeakClosure81

end
