module

public import CFSG.Monster.B.Geometry.ReducedWords
public import CFSG.Monster.B.Geometry.Coxeter

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.GroupActions.Exchange

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)

abbrev simpleSet : Set W := Set.range cs.simple

@[expose] def toSWord (ω : List ι) : List (simpleSet cs) := ω.map fun i => ⟨cs.simple i, i, rfl⟩

variable {cs}

@[simp] theorem length_toSWord (ω : List ι) : (toSWord cs ω).length = ω.length :=
  List.length_map _

@[simp] theorem wordProd_toSWord (ω : List ι) :
    wordProd (simpleSet cs) (toSWord cs ω) = cs.wordProd ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [toSWord, List.map_cons, CFSG.GroupActions.Exchange.wordProd_cons,
      CoxeterSystem.wordProd_cons] at ih ⊢
    rw [ih]

theorem toSWord_append (ω ω' : List ι) : toSWord cs (ω ++ ω') = toSWord cs ω ++ toSWord cs ω' :=
  List.map_append ..

theorem toSWord_take (ω : List ι) (j : ℕ) : toSWord cs (ω.take j) = (toSWord cs ω).take j :=
  List.map_take ..

theorem exists_toSWord_eq (l : List (simpleSet cs)) : ∃ ω : List ι, toSWord cs ω = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons s l ih =>
    obtain ⟨ω, rfl⟩ := ih
    obtain ⟨i, hi⟩ := s.2
    refine ⟨i :: ω, ?_⟩
    simp only [toSWord, List.map_cons]
    congr 1
    exact Subtype.ext hi

theorem toSWord_injective : Function.Injective (toSWord cs) := by
  intro ω ω' h
  refine List.map_injective_iff.mpr (fun i j hij => ?_) h
  exact cs.simple_injective (congrArg Subtype.val hij)

theorem wordLength_simpleSet (w : W) : wordLength (simpleSet cs) w = cs.length w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have := wordLength_wordProd_le (S := simpleSet cs) (toSWord cs ω)
    rw [wordProd_toSWord, length_toSWord] at this
    rw [hω.eq]
    exact this
  · obtain ⟨l, hl, hw⟩ := exists_length_eq_wordLength (S := simpleSet cs) (toSWord cs
      (cs.exists_isReduced w).choose)
    have hw0 : wordProd (simpleSet cs) (toSWord cs (cs.exists_isReduced w).choose) = w := by
      rw [wordProd_toSWord, ← (cs.exists_isReduced w).choose_spec.2]
    rw [hw0] at hl hw
    obtain ⟨ω, rfl⟩ := exists_toSWord_eq l
    rw [wordProd_toSWord] at hw
    rw [← hl, ← hw, length_toSWord]
    exact cs.length_wordProd_le ω

theorem isReduced_toSWord_iff {ω : List ι} :
    IsReduced (simpleSet cs) (toSWord cs ω) ↔ cs.IsReduced ω := by
  rw [CFSG.GroupActions.Exchange.IsReduced, wordProd_toSWord, wordLength_simpleSet,
    length_toSWord, CoxeterSystem.IsReduced, eq_comm]

theorem orderOf_simpleSet : ∀ s ∈ simpleSet cs, orderOf s = 2 := by
  rintro _ ⟨i, rfl⟩
  exact cs.orderOf_simple i

theorem pairOrder_simpleSet (i j : ι) :
    pairOrder (simpleSet cs) ⟨cs.simple i, i, rfl⟩ ⟨cs.simple j, j, rfl⟩ = M i j :=
  cs.orderOf_simple_mul_simple i j

theorem mem_leftDescents_simpleSet_iff {w : W} {i : ι} :
    (⟨cs.simple i, i, rfl⟩ : simpleSet cs) ∈ leftDescents (simpleSet cs) w ↔
      cs.IsLeftDescent w i := by
  change wordLength _ _ < wordLength _ _ ↔ _
  rw [wordLength_simpleSet, wordLength_simpleSet]
  rfl

theorem exchangeCondition_simpleSet : ExchangeCondition (simpleSet cs) := by
  intro s l hl hne hle
  obtain ⟨i, hi⟩ := s.2
  obtain ⟨ω, rfl⟩ := exists_toSWord_eq l
  have hω := isReduced_toSWord_iff.mp hl
  rw [wordProd_toSWord, wordLength_simpleSet, wordLength_simpleSet, ← hi] at hle
  have hd : cs.IsLeftDescent (cs.wordProd ω) i :=
    lt_of_le_of_ne hle (cs.length_simple_mul_ne _ i)
  obtain ⟨j, hj, hje, -⟩ := cs.exchangeCondition hω hd
  refine ⟨j, by simpa using hj, ?_⟩
  rw [← toSWord_take, ← toSWord_take, wordProd_toSWord, wordProd_toSWord, ← hi]
  have hsplit : cs.wordProd ω = cs.wordProd (ω.take j) * cs.simple (ω[j]'hj) *
      cs.wordProd (ω.drop (j + 1)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) ω, List.take_succ_eq_append_getElem hj]
    rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_singleton]
  have herase : cs.wordProd (ω.eraseIdx j) = cs.wordProd (ω.take j) *
      cs.wordProd (ω.drop (j + 1)) := by
    rw [List.eraseIdx_eq_take_drop_succ, cs.wordProd_append]
  rw [hsplit, herase] at hje
  have h1 : cs.simple i * cs.wordProd (ω.take j) * cs.simple (ω[j]'hj) =
      cs.wordProd (ω.take j) := by
    have := congrArg (· * (cs.wordProd (ω.drop (j + 1)))⁻¹) hje
    simpa [mul_assoc] using this
  rw [List.take_succ_eq_append_getElem hj, cs.wordProd_append, cs.wordProd_singleton]
  calc cs.simple i * cs.wordProd (ω.take j)
      = cs.simple i * cs.wordProd (ω.take j) * cs.simple (ω[j]'hj) * cs.simple (ω[j]'hj) := by
        rw [mul_assoc (cs.simple i * cs.wordProd (ω.take j)), cs.simple_mul_simple_self, mul_one]
    _ = cs.wordProd (ω.take j) * cs.simple (ω[j]'hj) := by rw [h1]

theorem triplePrefix_simpleSet [Finite W] : TriplePrefix (simpleSet cs) := by
  intro w J _ hJ
  set J' : Set ι := {i | (⟨cs.simple i, i, rfl⟩ : simpleSet cs) ∈ J}
  have hJl := isLongest_longest (cs := cs) J'
  obtain ⟨ω, hω, hωJ, hωp⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hJl.1
  have hdesc : ∀ i ∈ J', cs.IsLeftDescent w i := fun i hi =>
    mem_leftDescents_simpleSet_iff.mp (hJ _ hi)
  have hlen := length_longest_mul_of_forall_isLeftDescent hJl hdesc
  refine ⟨toSWord cs ω, isReduced_toSWord_iff.mpr hω, ?_, ?_, ?_⟩
  · intro s hs
    simp only [toSWord, List.mem_map] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact hωJ i hi
  · intro s hs
    obtain ⟨i, hi⟩ := s.2
    have hs_eq : s = ⟨cs.simple i, i, rfl⟩ := Subtype.ext hi.symm
    subst hs_eq
    have hs' : i ∈ J' := hs
    rw [wordProd_toSWord, hωp]
    exact mem_leftDescents_simpleSet_iff.mpr (hJl.isLeftDescent hs')
  · rw [wordProd_toSWord, hωp, wordLength_simpleSet, wordLength_simpleSet, wordLength_simpleSet,
      hJl.inv_eq]
    omega

end CFSG.Monster.B.Geometry
