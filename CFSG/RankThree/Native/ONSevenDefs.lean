module

public import CFSG.RankThree.Native.ONSevenData
public import CFSG.Sporadic.Schreier.ONOuterDefs

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier

@[expose] def onSevenQ : Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {g | g ∈ evalList onSevenSylowWords}

@[expose] def onSevenLine (j : Fin 57) : Equiv.Perm (Fin N) := evalS onSevenLineWords[j.val]!

@[expose] def onSevenRep (r : Fin 5) : Fin 57 :=
  ⟨onSevenRepIdx[r.val]! % 57, Nat.mod_lt _ (by norm_num)⟩

@[expose] def onSevenC (r : Fin 5) : Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {g | g ∈ evalList onSevenCentWords[r.val]!}

@[expose] def onSevenF (r : Fin 3) : Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {g | g ∈ evalList onSevenNormalWords[r.val]!}

@[expose] def onSevenTransporters (r : Fin 5) : List ONSevenTransporter :=
  (onSevenTransporterData[r.val]!).toList

@[expose] def onSevenTransporterPerm (t : ONSevenTransporter) : Equiv.Perm (Fin N) :=
  evalS t.word

theorem onSevenRep_val (r : Fin 5) : ((onSevenRep r : Fin 57) : ℕ) = onSevenRepIdx[r.val]! := by
  fin_cases r <;> rfl

theorem onSeven_mem_P :
    onSevenQ ≤ Pv ∧ (∀ j, onSevenLine j ∈ Pv) ∧ (∀ r, onSevenC r ≤ Pv) ∧
      (∀ r, onSevenF r ≤ Pv) ∧ ∀ t : ONSevenTransporter, onSevenTransporterPerm t ∈ Pv :=
  ⟨closure_evalList_le _, fun _ => evalS_mem _, fun _ => closure_evalList_le _,
    fun _ => closure_evalList_le _, fun _ => evalS_mem _⟩

end CFSG.RankThree.Native
