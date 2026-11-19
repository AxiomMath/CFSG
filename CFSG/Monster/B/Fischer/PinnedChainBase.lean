
module

public import CFSG.Monster.B.Fischer.PinnedChainData
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainOrderGenerators
public meta import CFSG.Monster.B.Fischer.PinnedChainData
public meta import CFSG.Monster.B.Co2.PermArr
public import CFSG.Monster.B.Fischer.PinnedChainInputs

@[expose] public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22StrongArrs_get {j : ℕ} (hj : j < 19) : fi22StrongArrs[j]! = fi22ChainStrong j := by
  rw [fi22StrongArrs, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

noncomputable def fi22StrongPerm (j : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22ChainStrong j)

noncomputable def fi22GenPerm (k : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22ChainGen k)

noncomputable def fi22Chain : RawSchreierDatum 3510 where
  degree_pos := by decide
  originalCount := 2
  strongCount := 19
  baseCount := 6
  originalCount_le := by decide
  original := Vector.ofFn fun k : Fin 2 => fi22GenPerm k
  strong := Vector.ofFn fun j : Fin 19 => fi22StrongPerm j
  base := #v[0, 1, 2, 3, 6, 4]
  base_distinct := by decide
  derivation j _ := toLetters j.val (fi22Derivation j.val)

noncomputable def fi22P : Subgroup (Equiv.Perm (Fin 3510)) := fi22Chain.originalSubgroup

theorem fi22Chain_strong_get (j : Fin fi22Chain.strongCount) :
    fi22Chain.strong.get j = fi22StrongPerm j := by
  change (Vector.ofFn fun j : Fin 19 => fi22StrongPerm j).get j = fi22StrongPerm j
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem fi22Chain_original_get (k : Fin fi22Chain.originalCount) :
    fi22Chain.original.get k = fi22GenPerm k := by
  change (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).get k = fi22GenPerm k
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem fi22Chain_base : fi22Chain.base.toList.map Fin.val = fi22ChainBase := by decide

end CFSG.Monster.B.Fischer
