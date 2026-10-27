module

public import CFSG.Monster.B.Geometry.CoxeterWords

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.GroupActions.Exchange

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)

variable (M) in
@[expose] def parMatrix (J : Set ι) : CoxeterMatrix J where
  M := M.M.submatrix Subtype.val Subtype.val
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal i
  off_diagonal i j h := M.off_diagonal i j fun e => h (Subtype.ext e)

@[simp] theorem parMatrix_apply (J : Set ι) (i j : J) : parMatrix M J i j = M i j := rfl

variable (J : Set ι)

theorem isLiftable_parMatrix : (parMatrix M J).IsLiftable fun j => cs.simple (j : ι) :=
  fun i j => cs.simple_mul_simple_pow i j

@[expose] def parToGroup : (parMatrix M J).Group →* W :=
  (parMatrix M J).toCoxeterSystem.lift ⟨fun j => cs.simple j, isLiftable_parMatrix cs J⟩

@[simp] theorem parToGroup_simple (j : J) :
    parToGroup cs J ((parMatrix M J).simple j) = cs.simple j := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, parToGroup, CoxeterSystem.lift_apply_simple]

theorem parToGroup_wordProd (ω : List J) :
    parToGroup cs J ((parMatrix M J).toCoxeterSystem.wordProd ω) = cs.wordProd (ω.map (↑)) := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, List.map_cons, CoxeterSystem.wordProd_cons,
      CoxeterMatrix.toCoxeterSystem_simple, parToGroup_simple]

theorem parToGroup_mem (v : (parMatrix M J).Group) : parToGroup cs J v ∈ cs.parabolic J := by
  obtain ⟨ω, rfl⟩ := (parMatrix M J).toCoxeterSystem.wordProd_surjective v
  rw [parToGroup_wordProd]
  exact cs.wordProd_mem_parabolic fun i hi => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact j.2

@[expose] def parToPar : (parMatrix M J).Group →* cs.parabolic J :=
  (parToGroup cs J).codRestrict _ (parToGroup_mem cs J)

@[simp] theorem coe_parToPar (v : (parMatrix M J).Group) :
    (parToPar cs J v : W) = parToGroup cs J v := rfl

abbrev parSimpleSet : Set (cs.parabolic J) := Subtype.val ⁻¹' (cs.simple '' J)

theorem orderOf_parSimpleSet : ∀ s ∈ parSimpleSet cs J, orderOf s = 2 := by
  rintro s ⟨j, -, hj⟩
  rw [← Subgroup.orderOf_coe, ← hj, cs.orderOf_simple]

@[expose] def parLetter (j : J) : parSimpleSet cs J :=
  ⟨⟨cs.simple j, cs.simple_mem_parabolic j.2⟩, j, j.2, rfl⟩

@[expose] def parToSWord (l : List (parSimpleSet cs J)) : List (simpleSet cs) :=
  l.map fun s : parSimpleSet cs J => ⟨((s : cs.parabolic J) : W), Set.image_subset_range _ _ s.2⟩

@[simp] theorem length_parToSWord (l : List (parSimpleSet cs J)) :
    (parToSWord cs J l).length = l.length := by
  simp [parToSWord]

theorem wordProd_parToSWord (l : List (parSimpleSet cs J)) :
    wordProd (simpleSet cs) (parToSWord cs J l) =
      ((wordProd (parSimpleSet cs J) l : cs.parabolic J) : W) := by
  induction l with
  | nil => simp [parToSWord]
  | cons s l ih =>
    simp only [parToSWord, List.map_cons, CFSG.GroupActions.Exchange.wordProd_cons,
      Subgroup.coe_mul] at ih ⊢
    rw [ih]

theorem parToSWord_take (l : List (parSimpleSet cs J)) (j : ℕ) :
    parToSWord cs J (l.take j) = (parToSWord cs J l).take j := by
  simp [parToSWord, List.map_take]

theorem wordProd_map_parLetter (ω : List J) :
    ((wordProd (parSimpleSet cs J) (ω.map (parLetter cs J)) : cs.parabolic J) : W) =
      cs.wordProd (ω.map (↑)) := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    simp only [List.map_cons, CFSG.GroupActions.Exchange.wordProd_cons, Subgroup.coe_mul,
      CoxeterSystem.wordProd_cons, ih]
    rfl

theorem exists_map_val_eq {ω : List ι} (h : ∀ i ∈ ω, i ∈ J) : ∃ ω' : List J, ω'.map (↑) = ω := by
  induction ω with
  | nil => exact ⟨[], rfl⟩
  | cons i ω ih =>
    obtain ⟨ω', hω'⟩ := ih fun k hk => h k (by simp [hk])
    exact ⟨⟨i, h i (by simp)⟩ :: ω', by simp [hω']⟩

theorem exists_parWord (w : cs.parabolic J) :
    ∃ ω : List J, cs.IsReduced (ω.map (↑)) ∧ cs.wordProd (ω.map (↑)) = w := by
  obtain ⟨ω, hω, hJ, hωw⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic w.2
  obtain ⟨ω', rfl⟩ := exists_map_val_eq J hJ
  exact ⟨ω', hω, hωw⟩

theorem exchangeWordProd_mem_closure {G : Type*} [Group G] {S : Set G} (l : List S) :
    wordProd S l ∈ Subgroup.closure S := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons s l ih => exact Subgroup.mul_mem _ (Subgroup.subset_closure s.2) ih

theorem closure_parSimpleSet : Subgroup.closure (parSimpleSet cs J) = ⊤ := by
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨ω, -, hωw⟩ := exists_parWord cs J w
  have hw : wordProd (parSimpleSet cs J) (ω.map (parLetter cs J)) = w :=
    Subtype.ext ((wordProd_map_parLetter cs J ω).trans hωw)
  rw [← hw]
  exact exchangeWordProd_mem_closure _

theorem wordLength_parSimpleSet (w : cs.parabolic J) :
    wordLength (parSimpleSet cs J) w = cs.length w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, hωw⟩ := exists_parWord cs J w
    have hw : wordProd (parSimpleSet cs J) (ω.map (parLetter cs J)) = w :=
      Subtype.ext ((wordProd_map_parLetter cs J ω).trans hωw)
    have := wordLength_wordProd_le (S := parSimpleSet cs J) (ω.map (parLetter cs J))
    rw [hw, List.length_map] at this
    rw [← hωw, hω.eq, List.length_map]
    exact this
  · obtain ⟨l₀, hl₀⟩ := exists_wordProd_eq_of_mem_closure (orderOf_parSimpleSet cs J)
      (by rw [closure_parSimpleSet]; exact Subgroup.mem_top w)
    obtain ⟨l, hl, hlw⟩ := exists_length_eq_wordLength l₀
    rw [hl₀] at hl hlw
    rw [← hl, ← hlw, ← wordProd_parToSWord, ← wordLength_simpleSet, ← length_parToSWord cs J l]
    exact wordLength_wordProd_le _

theorem isReduced_parToSWord_iff {l : List (parSimpleSet cs J)} :
    IsReduced (simpleSet cs) (parToSWord cs J l) ↔ IsReduced (parSimpleSet cs J) l := by
  rw [CFSG.GroupActions.Exchange.IsReduced, CFSG.GroupActions.Exchange.IsReduced,
    wordProd_parToSWord, wordLength_simpleSet, wordLength_parSimpleSet, length_parToSWord]

theorem exchangeCondition_parSimpleSet : ExchangeCondition (parSimpleSet cs J) := by
  intro s l hl hne hle
  have hle' : wordLength (simpleSet cs)
      (((⟨((s : cs.parabolic J) : W), Set.image_subset_range _ _ s.2⟩ : simpleSet cs) : W) *
        wordProd (simpleSet cs) (parToSWord cs J l)) ≤
      wordLength (simpleSet cs) (wordProd (simpleSet cs) (parToSWord cs J l)) := by
    rw [wordProd_parToSWord, wordLength_simpleSet, wordLength_simpleSet]
    rw [wordLength_parSimpleSet, wordLength_parSimpleSet] at hle
    exact hle
  obtain ⟨j, hj, he⟩ := exchangeCondition_simpleSet (cs := cs) _ (parToSWord cs J l)
    ((isReduced_parToSWord_iff cs J).mpr hl) (by simpa [parToSWord] using hne) hle'
  refine ⟨j, by simpa using hj, Subtype.ext ?_⟩
  rw [← parToSWord_take, ← parToSWord_take, wordProd_parToSWord, wordProd_parToSWord] at he
  simpa using he

@[expose] def parIndex (s : parSimpleSet cs J) : J :=
  ⟨Classical.choose (show ∃ j, j ∈ J ∧ cs.simple j = ((s : cs.parabolic J) : W) from s.2),
    (Classical.choose_spec (show ∃ j, j ∈ J ∧ cs.simple j = ((s : cs.parabolic J) : W)
      from s.2)).1⟩

theorem simple_parIndex (s : parSimpleSet cs J) :
    cs.simple (parIndex cs J s) = ((s : cs.parabolic J) : W) :=
  (Classical.choose_spec (show ∃ j, j ∈ J ∧ cs.simple j = ((s : cs.parabolic J) : W)
    from s.2)).2

theorem parIndex_parLetter (j : J) : parIndex cs J (parLetter cs J j) = j :=
  Subtype.ext (cs.simple_injective (simple_parIndex cs J _))

theorem braidRel_parSimpleSet :
    BraidRel (parSimpleSet cs J) fun s => (parMatrix M J).simple (parIndex cs J s) := by
  intro s t _ _
  have hst : orderOf ((s : cs.parabolic J) * t) =
      parMatrix M J (parIndex cs J s) (parIndex cs J t) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, ← simple_parIndex cs J s,
      ← simple_parIndex cs J t, cs.orderOf_simple_mul_simple]
    rfl
  have h1 := (parMatrix M J).toCoxeterSystem.simple_mul_simple_self
  simp only [CoxeterMatrix.toCoxeterSystem_simple] at h1
  rw [hst, altProd_eq_altProd_iff (h1 _) (h1 _)]
  have h2 := (parMatrix M J).toCoxeterSystem.simple_mul_simple_pow (parIndex cs J s)
    (parIndex cs J t)
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using h2

theorem exists_parOfGroup : ∃ F : cs.parabolic J →* (parMatrix M J).Group,
    ∀ s : parSimpleSet cs J, F s = (parMatrix M J).simple (parIndex cs J s) := by
  have h1 := (parMatrix M J).toCoxeterSystem.simple_mul_simple_self
  simp only [CoxeterMatrix.toCoxeterSystem_simple] at h1
  exact (exchange_coxeter_universal_property (orderOf_parSimpleSet cs J)
    (closure_parSimpleSet cs J) (exchangeCondition_parSimpleSet cs J) _
    (fun s => by rw [sq, h1]) (braidRel_parSimpleSet cs J)).exists

@[expose] def parOfGroup : cs.parabolic J →* (parMatrix M J).Group :=
  Classical.choose (exists_parOfGroup cs J)

theorem parOfGroup_parSimpleSet (s : parSimpleSet cs J) :
    parOfGroup cs J s = (parMatrix M J).simple (parIndex cs J s) :=
  Classical.choose_spec (exists_parOfGroup cs J) s

@[simp] theorem parOfGroup_simple (j : J) :
    parOfGroup cs J ⟨cs.simple j, cs.simple_mem_parabolic j.2⟩ = (parMatrix M J).simple j := by
  have := parOfGroup_parSimpleSet cs J (parLetter cs J j)
  rwa [parIndex_parLetter] at this

theorem parToGroup_parOfGroup (w : cs.parabolic J) : parToGroup cs J (parOfGroup cs J w) = w := by
  have h : (parToGroup cs J).comp (parOfGroup cs J) = (cs.parabolic J).subtype := by
    refine MonoidHom.eq_of_eqOn_dense (closure_parSimpleSet cs J) fun s hs => ?_
    change parToGroup cs J (parOfGroup cs J (⟨s, hs⟩ : parSimpleSet cs J)) = s
    rw [parOfGroup_parSimpleSet, parToGroup_simple, simple_parIndex]
  exact congrArg (fun F : cs.parabolic J →* W => F w) h

theorem parOfGroup_parToPar (v : (parMatrix M J).Group) :
    parOfGroup cs J (parToPar cs J v) = v := by
  have h : (parOfGroup cs J).comp (parToPar cs J) = MonoidHom.id _ := by
    refine (parMatrix M J).toCoxeterSystem.ext_simple fun j => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, CoxeterMatrix.toCoxeterSystem_simple]
    have e : parToPar cs J ((parMatrix M J).simple j) =
        ⟨cs.simple j, cs.simple_mem_parabolic j.2⟩ :=
      Subtype.ext (parToGroup_simple cs J j)
    rw [e, parOfGroup_simple]
  exact congrArg (fun F : (parMatrix M J).Group →* (parMatrix M J).Group => F v) h

theorem parOfGroup_parToGroup (v : (parMatrix M J).Group) :
    parOfGroup cs J ⟨parToGroup cs J v, parToGroup_mem cs J v⟩ = v :=
  parOfGroup_parToPar cs J v

theorem parOfGroup_injective : Function.Injective (parOfGroup cs J) := fun w w' h =>
  Subtype.ext (by rw [← parToGroup_parOfGroup cs J w, h, parToGroup_parOfGroup])

theorem parToGroup_injective : Function.Injective (parToGroup cs J) := fun v v' h => by
  rw [← parOfGroup_parToGroup cs J v, ← parOfGroup_parToGroup cs J v']
  congr 1
  exact Subtype.ext h

theorem parOfGroup_eq_iff {w : cs.parabolic J} {v : (parMatrix M J).Group} :
    parOfGroup cs J w = v ↔ (w : W) = parToGroup cs J v := by
  constructor
  · rintro rfl
    exact (parToGroup_parOfGroup cs J w).symm
  · intro h
    rw [← parOfGroup_parToGroup cs J v]
    congr 1
    exact Subtype.ext h

theorem parOfGroup_eq_simple_iff {w : cs.parabolic J} {j : J} :
    parOfGroup cs J w = (parMatrix M J).simple j ↔ (w : W) = cs.simple j := by
  rw [parOfGroup_eq_iff, parToGroup_simple]

include cs in
theorem finite_parGroup [Finite W] : Finite (parMatrix M J).Group :=
  Finite.of_injective _ (parToGroup_injective cs J)

theorem length_parToGroup (v : (parMatrix M J).Group) :
    cs.length (parToGroup cs J v) = (parMatrix M J).toCoxeterSystem.length v := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, rfl⟩ := (parMatrix M J).toCoxeterSystem.exists_isReduced v
    rw [parToGroup_wordProd, hω.eq]
    exact (cs.length_wordProd_le _).trans (by simp)
  · obtain ⟨ω, hω, hωw⟩ := exists_parWord cs J ⟨parToGroup cs J v, parToGroup_mem cs J v⟩
    have hωw' : cs.wordProd (ω.map (↑)) = parToGroup cs J v := hωw
    have hv : v = (parMatrix M J).toCoxeterSystem.wordProd ω := by
      apply parToGroup_injective cs J
      rw [parToGroup_wordProd]
      exact hωw'.symm
    have h1 := (parMatrix M J).toCoxeterSystem.length_wordProd_le ω
    have h2 := hω.eq
    rw [hωw', List.length_map] at h2
    rw [h2, ← hv] at *
    exact h1

theorem length_parOfGroup (w : cs.parabolic J) :
    (parMatrix M J).toCoxeterSystem.length (parOfGroup cs J w) = cs.length w := by
  rw [← length_parToGroup cs J, parToGroup_parOfGroup]

theorem parOfGroup_mem_parabolic_iff (I : Set J) (w : cs.parabolic J) :
    parOfGroup cs J w ∈ (parMatrix M J).toCoxeterSystem.parabolic I ↔
      (w : W) ∈ cs.parabolic (Subtype.val '' I) := by
  constructor
  · intro h
    rw [← parToGroup_parOfGroup cs J w]
    obtain ⟨ω, -, hI, hω⟩ :=
      (parMatrix M J).toCoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic h
    rw [← hω, parToGroup_wordProd]
    exact cs.wordProd_mem_parabolic fun i hi => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact ⟨j, hI j hj, rfl⟩
  · intro h
    obtain ⟨ω, hω, hωw⟩ := exists_parWord cs J w
    have hv : parOfGroup cs J w = (parMatrix M J).toCoxeterSystem.wordProd ω := by
      rw [parOfGroup_eq_iff, parToGroup_wordProd]
      exact hωw.symm
    rw [hv]
    refine (parMatrix M J).toCoxeterSystem.wordProd_mem_parabolic fun j hj => ?_
    have h' : cs.wordProd (ω.map (↑)) ∈ cs.parabolic (Subtype.val '' I) := by
      rw [hωw]
      exact h
    obtain ⟨k, hk, hkj⟩ := mem_of_isReduced_of_mem_parabolic cs hω h' (List.mem_map_of_mem hj)
    rwa [← Subtype.ext hkj]

theorem parToGroup_mem_parabolic_iff (I : Set J) (v : (parMatrix M J).Group) :
    parToGroup cs J v ∈ cs.parabolic (Subtype.val '' I) ↔
      v ∈ (parMatrix M J).toCoxeterSystem.parabolic I := by
  rw [← parOfGroup_mem_parabolic_iff cs J I ⟨_, parToGroup_mem cs J v⟩, parOfGroup_parToGroup]

theorem parToGroup_longest [Finite W] (I : Set J) :
    parToGroup cs J (longest (parMatrix M J).toCoxeterSystem I) =
      longest cs (Subtype.val '' I) := by
  have := finite_parGroup cs J
  have hl := isLongest_longest (cs := (parMatrix M J).toCoxeterSystem) I
  refine IsLongest.eq_longest ⟨(parToGroup_mem_parabolic_iff cs J I _).mpr hl.1, fun w hw => ?_⟩
  have hwJ : w ∈ cs.parabolic J :=
    cs.parabolic_mono (Set.image_subset_iff.mpr fun j _ => j.2) hw
  have h1 := (parOfGroup_mem_parabolic_iff cs J I ⟨w, hwJ⟩).mpr hw
  have h2 := hl.2 _ h1
  rw [length_parOfGroup] at h2
  rw [length_parToGroup]
  exact h2

end CFSG.Monster.B.Geometry
