
module

public import CFSG.Sporadic.Fi24.FaithfulBase

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev letters : Array Table := chainLetters orb

noncomputable abbrev lv1 : Array ℕ := levelLetters letters chainBase 1

structure ActionFacts : Prop where
  beta_inv : invOK nPts orb.beta (invT nPts orb.beta) = true
  slp_ok : slpOK chainWords = true
  words_size : chainWords.size = 13
  word0 : chainWords[0]! = [1]
  word1 : chainWords[1]! = [2]

theorem chainBase_get_lt {t : ℕ} (ht : t < chainBase.size) : chainBase[t]! < 306936 := by
  have := chainBase_lt t (by rw [chainBase_size] at ht; exact ht)
  rwa [nPts_eq] at this

theorem chainBase_zero : chainBase[0]! = 0 := by decide

theorem chainBase_one : chainBase[1]! = 305530 := by decide

theorem tree_size_of {l v : ℕ} (hv : [306936, 275264, 218400, 93312, 243, 3][l]? = some v) :
    chainSizes[l]! = v := by
  unfold chainSizes
  rw [getElem!_def, hv]

noncomputable abbrev root : Fin 306936 := ⟨0, by norm_num⟩

@[expose] def InTree (T : Tree) (p : ℕ) : Prop :=
  ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p

instance (T : Tree) (p : ℕ) : Decidable (InTree T p) := by unfold InTree; infer_instance

theorem inTreeB_iff (T : Tree) (p : ℕ) : inTreeB T p = true ↔ InTree T p := by
  simp [inTreeB, InTree]

@[expose] def InOrbOne (p : Fin 306936) : Prop :=
  ∃ w : List ℕ, (∀ l ∈ w, l ∈ lv1) ∧ w.foldr (fun l z => ap letters[l]! z) p.val = 305530

@[expose] noncomputable def subLab (p : Fin 306936) : Fin 3 := by
  classical
  exact if p.val = 0 then 0 else if InOrbOne p then 1 else 2

theorem subLab_eq_zero {p : Fin 306936} : subLab p = 0 ↔ p = root := by
  unfold subLab
  constructor
  · intro h
    by_contra hp
    have hp' : p.val ≠ 0 := fun e => hp (Fin.ext e)
    rw [ite_eq_right hp'] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem card_subLab_zero :
    (Finset.univ.filter (fun p : Fin 306936 => subLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨root, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact subLab_eq_zero

@[expose] def subSizes : Fin 3 → ℕ := ![1, 275264, 31671]

theorem subSizes_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 306936 → S = {0} ∨ S = Finset.univ := by
  decide

end CFSG.Sporadic.Fi24
