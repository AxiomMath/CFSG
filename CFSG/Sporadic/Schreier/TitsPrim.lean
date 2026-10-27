module

public import CFSG.Sporadic.Schreier.TitsStab
public import CFSG.Sporadic.Schreier.TitsPrimCheck
public import CFSG.Certificates.MergePrimitivity

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem range_eq_closure_of {G M : Type*} [Group G] [Group M] {T : Set G} {U : Set M}
    (φ : Subgroup.closure T →* M)
    (h1 : ∀ t (ht : t ∈ T), φ ⟨t, Subgroup.subset_closure ht⟩ ∈ U)
    (h2 : ∀ u ∈ U, ∃ t, ∃ ht : t ∈ T, φ ⟨t, Subgroup.subset_closure ht⟩ = u) :
    φ.range = Subgroup.closure U := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 fun u hu => ?_)
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact Subgroup.subset_closure (h1 t ht)
    | one => rw [show (⟨1, _⟩ : Subgroup.closure T) = 1 from rfl, map_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      rw [show (⟨x * y, mul_mem hx hy⟩ : Subgroup.closure T) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl,
        map_mul]
      exact mul_mem ihx ihy
    | inv x hx ih =>
      rw [show (⟨x⁻¹, inv_mem hx⟩ : Subgroup.closure T) = (⟨x, hx⟩)⁻¹ from rfl, map_inv]
      exact inv_mem ih
  · obtain ⟨t, ht, rfl⟩ := h2 u hu
    exact ⟨_, rfl⟩

theorem titsDLineAct_range :
    titsDLineAct.range = Subgroup.closure (Set.range fun j : Fin 2 => titsDStar j) :=
  range_eq_closure_of titsDLineAct
    (fun _ ⟨j, hj⟩ => by subst hj; exact ⟨j, (titsDLineAct_dGen j.2).symm⟩)
    (fun _ ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, by rw [← hj]; exact titsDLineAct_dGen j.2⟩)

theorem titsDFlagAct_range :
    titsDFlagAct.range = Subgroup.closure (Set.range fun j : Fin 2 => titsDFlag j) :=
  range_eq_closure_of titsDFlagAct
    (fun _ ⟨j, hj⟩ => by subst hj; exact ⟨j, (titsDFlagAct_dGen j.2).symm⟩)
    (fun _ ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, by rw [← hj]; exact titsDFlagAct_dGen j.2⟩)

@[expose] def titsH0 : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure {g | ∃ j < 13, titsT j = g ∧ g 0 = 0}

theorem titsT_fix_iff
    {j : ℕ} (hj : j < 13) : titsT j 0 = 0 ↔ 2 ≤ j := by
  have hidx := titsPrim_check.1
  have hmem : j ∈ titsH0Idx ↔ 2 ≤ j := by
    rw [hidx]
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    omega
  rw [← hmem, titsH0Idx, List.mem_filter, List.mem_range, beq_iff_eq,
    (titsT_rep hj).apply (by norm_num : 0 < 1755)]
  simp only [hj, true_and]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

@[expose] def titsH0Gen (i : ℕ) : Equiv.Perm (Fin 1755) := titsT (i + 2)

theorem titsH0Arrs_size : titsH0Arrs.size = 11 := by
  rw [titsH0Arrs, List.size_toArray, List.length_map, titsPrim_check.1]
  rfl

theorem titsH0_rep :
    ∀ i < titsH0Arrs.size, Rep 1755 titsH0Arrs[i]! (titsH0Gen i) := by
  intro i hi
  rw [titsH0Arrs_size] at hi
  have e : titsH0Arrs[i]! = titsDerivedArrs[i + 2]! := by
    rw [titsH0Arrs, getElem!_pos _ i (by simp [titsPrim_check.1]; omega)]
    simp only [List.getElem_toArray, List.getElem_map, titsPrim_check.1]
    congr 1
    interval_cases i <;> rfl
  rw [e]
  exact titsT_rep (by omega)

theorem titsH0_eq_genGroup :
    titsH0 = genGroup titsH0Arrs titsH0Gen := by
  rw [titsH0, genGroup, titsH0Arrs_size]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl, h0⟩
    have h2 := (titsT_fix_iff hj).1 h0
    exact ⟨j - 2, by omega, by rw [titsH0Gen, show j - 2 + 2 = j by omega]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + 2, by omega, rfl, (titsT_fix_iff (by omega)).2 (by omega)⟩

theorem titsH0_le_titsD : titsH0 ≤ titsD :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hj, e, _⟩ => e ▸ titsT_mem_titsD hj

theorem titsH0_fix : ∀ h ∈ titsH0, h 0 = 0 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, _, _, h0⟩ := hx
    exact h0
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

@[expose] def titsH0Reps : List ℕ := [0, 1, 6, 24, 87]

theorem titsH0_orbit_eq
    {c : ℕ} (hc : c < 5) :
    MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!) =
      {x : Fin 1755 | titsH0Forest.1[(x : ℕ)]! = c} := by
  have h := orbit_eq_label titsPrim_check.2.2.2.1 titsH0_rep hc
  rw [← titsH0_eq_genGroup] at h
  rw [← h]
  congr 1
  apply Fin.ext
  interval_cases c <;> rfl

theorem titsH0_label_lt
    (x : Fin 1755) : titsH0Forest.1[(x : ℕ)]! < 5 :=
  (orbitLabelOK_parts titsPrim_check.2.2.2.1).1 x x.2

theorem titsH0_orbit_ncard
    {c : ℕ} (hc : c < 5) :
    (MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!)).ncard = titsStabSizes[c]! := by
  rw [titsH0_orbit_eq hc, ncard_label, ← titsPrim_check.2.2.2.2.1]
  rw [getElem!_pos _ c (by simp; omega)]
  simp

theorem titsH0_orbit_least
    {c : ℕ} (hc : c < 5) :
    ∀ x ∈ MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!), titsH0Reps[c]! ≤ (x : ℕ) := by
  intro x hx
  rw [titsH0_orbit_eq hc, Set.mem_ofPred_eq] at hx
  have := of_decide_eq_true (allLt_spec titsPrim_check.2.2.2.2.2.1 x.2)
  rw [hx] at this
  simpa [titsH0Reps] using this

theorem titsH0_orbit_cover
    (x : Fin 1755) :
    ∃ c < 5, x ∈ MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!) :=
  ⟨_, titsH0_label_lt x, by rw [titsH0_orbit_eq (titsH0_label_lt x)]; rfl⟩

theorem titsDArrs_rep
    (j : Fin 2) : Rep 1755 titsDArrs[(j : ℕ)]! (titsDGen j) := by
  rw [titsDArrs_get j.2]
  exact titsDArr_rep j.2

theorem CERT_Tits_merge_validity :
    titsH0 ≤ titsD ∧ (∀ h ∈ titsH0, h 0 = 0) ∧
    titsStabSizes = [1, 10, 80, 640, 1024] ∧ titsStabReps = [1, 6, 24, 87] ∧
    (∀ c < 5, (MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!)).ncard = titsStabSizes[c]! ∧
      ∀ x ∈ MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!), titsH0Reps[c]! ≤ (x : ℕ)) ∧
    (∀ x : Fin 1755, ∃ c < 5, x ∈ MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!)) ∧
    (∀ l < 4, (titsOrigMerge l).length = 1753 ∧
      ValidInvariantMerge (fun j : Fin 2 => titsDGen j) 0 (finPt 1755 titsStabReps[l]!)
        (titsOrigMerge l)) := by
  refine ⟨titsH0_le_titsD, titsH0_fix, titsPrim_check.2.2.1, titsPrim_check.2.1,
    fun c hc => ⟨titsH0_orbit_ncard hc, titsH0_orbit_least hc⟩, titsH0_orbit_cover,
    fun l hl => ⟨(titsPrim_check.2.2.2.2.2.2.1 l hl).1, ?_⟩⟩
  have h := (titsPrim_check.2.2.2.2.2.2.1 l hl).2
  have hx : ((finPt 1755 titsStabReps[l]! : Fin 1755) : ℕ) = titsStabReps[l]! := by
    apply finPt_val
    rw [titsPrim_check.2.1]
    interval_cases l <;> decide
  refine validInvariantMerge_of_mergeOK titsDArrs_rep ?_
  rw [hx]
  exact h

theorem CERT_Tits_derived_primitive :
    MulAction.IsPreprimitive titsD (Fin 1755) := by
  have htrans : MulAction.IsPretransitive
      (Subgroup.closure (Set.range fun j : Fin 2 => titsDGen j)) (Fin 1755) :=
    titsD_pretransitive
  obtain ⟨-, -, -, hreps, -, -, hmerge⟩ := CERT_Tits_merge_validity
  refine stabilizer_orbit_merge_primitivity (fun j : Fin 2 => titsDGen j) 0 titsH0
    titsH0_le_titsD titsH0_fix (xs := fun j : Fin 4 => finPt 1755 titsStabReps[(j : ℕ)]!) ?_
    (fun j => ⟨_, (hmerge j j.2).2⟩)
  intro x hx
  obtain ⟨c, hc, hxc⟩ := titsH0_orbit_cover x
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨⟨h, hh⟩, rfl⟩ := hxc
    exact hx (titsH0_fix h hh)
  obtain ⟨⟨h, hh⟩, e⟩ := hxc
  refine ⟨⟨c - 1, by omega⟩, h, hh, ?_⟩
  rw [← e]
  show h _ = h _
  congr 2
  rw [hreps]
  interval_cases c <;> first | rfl | exact absurd rfl hc0

@[expose] def titsNLine :
    titsN →* Equiv.Perm (Fin 2925) :=
  titsDLineAct.comp (Subgroup.inclusion titsN_le_titsD)

theorem getD_eq_get {α : Type*} {l : List α} {i : ℕ} {d : α} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

@[expose] def titsNStarGen (i : ℕ) : Equiv.Perm (Fin 2925) :=
  wordIn 13 titsTStar (titsNWords.getD i [])

theorem titsNWords_length : titsNWords.length = 4 :=
  titsLocalChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsNStarArrs_size : titsNStarArrs.size = 4 := by
  rw [titsNStarArrs, List.size_toArray, List.length_map, titsNWords_length]

theorem titsNStar_rep :
    ∀ i < titsNStarArrs.size, Rep 2925 titsNStarArrs[i]! (titsNStarGen i) := by
  intro i hi
  rw [titsNStarArrs_size] at hi
  have hi' : i < titsNWords.length := by rw [titsNWords_length]; exact hi
  have e : titsNStarArrs[i]! = wordArr 2925 titsTStarArrs titsNWords[i] := by
    rw [titsNStarArrs, getElem!_pos _ i (by simpa [titsNWords_length] using hi)]
    simp
  rw [e, titsNStarGen, getD_eq_get hi']
  exact rep_wordArr_tstar (titsLocalWords_letters titsLocalWords_mem.2.2.1 (List.getElem_mem _))

theorem titsNLine_word
    {w : List ℤ} (hw : wordIn 13 titsT w ∈ titsN) :
    titsNLine ⟨wordIn 13 titsT w, hw⟩ = wordIn 13 titsTStar w :=
  titsDLineAct_word w

theorem titsNLine_range :
    titsNLine.range = genGroup titsNStarArrs titsNStarGen := by
  rw [genGroup, titsNStarArrs_size]
  refine range_eq_closure_of (T := {g | ∃ w ∈ titsNWords, wordIn 13 titsT w = g}) titsNLine
    ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    refine ⟨i, by rw [← titsNWords_length]; exact hi, ?_⟩
    rw [titsNStarGen, getD_eq_get hi]
    exact (titsNLine_word _).symm
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : i < titsNWords.length := by rw [titsNWords_length]; exact hi
    refine ⟨wordIn 13 titsT titsNWords[i], ⟨_, List.getElem_mem hi', rfl⟩, ?_⟩
    rw [titsNStarGen, getD_eq_get hi']
    exact titsNLine_word _

theorem titsNLine_orbit_eq
    {c : ℕ} (hc : c < 6) :
    MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!) =
      {x : Fin 2925 | titsNForest.1[(x : ℕ)]! = c} := by
  have h := orbit_eq_label titsPrim_check.2.2.2.2.2.2.2.2.2.1 titsNStar_rep hc
  rw [← titsNLine_range] at h
  rw [← h]
  congr 1
  apply Fin.ext
  show titsOtherReps[c]! % 2925 = (#[0, 1, 7, 27, 107, 141] : Array ℕ)[c]! % 2925
  rw [titsPrim_check.2.2.2.2.2.2.2.1]
  interval_cases c <;> rfl

theorem titsNLine_label_lt
    (x : Fin 2925) : titsNForest.1[(x : ℕ)]! < 6 :=
  (orbitLabelOK_parts titsPrim_check.2.2.2.2.2.2.2.2.2.1).1 x x.2

theorem titsNLine_orbit_ncard
    {c : ℕ} (hc : c < 6) :
    (MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!)).ncard =
      titsOtherSizes[c]! := by
  rw [titsNLine_orbit_eq hc, ncard_label, ← titsPrim_check.2.2.2.2.2.2.2.2.2.2.1]
  rw [getElem!_pos _ c (by simp; omega)]
  simp

theorem titsNLine_orbit_least
    {c : ℕ} (hc : c < 6) :
    ∀ x ∈ MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!),
      titsOtherReps[c]! ≤ (x : ℕ) := by
  intro x hx
  rw [titsNLine_orbit_eq hc, Set.mem_ofPred_eq] at hx
  have := of_decide_eq_true (allLt_spec titsPrim_check.2.2.2.2.2.2.2.2.2.2.2.1 x.2)
  rw [hx] at this
  rw [titsPrim_check.2.2.2.2.2.2.2.1]
  interval_cases c <;> exact this

theorem titsNLine_orbit_cover
    (x : Fin 2925) :
    ∃ c < 6, x ∈ MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!) :=
  ⟨_, titsNLine_label_lt x, by rw [titsNLine_orbit_eq (titsNLine_label_lt x)]; rfl⟩

theorem titsNLine_fix
    (g : titsN) : titsNLine g 0 = 0 := titsN_fix g

theorem titsDStarArrs_rep
    (j : Fin 2) : Rep 2925 titsDStarArrs[(j : ℕ)]! (titsDStar j) :=
  titsDStar_rep j.2

theorem titsDLine_primitive :
    MulAction.IsPreprimitive (Subgroup.closure (Set.range fun j : Fin 2 => titsDStar j))
      (Fin 2925) := by
  have htrans : MulAction.IsPretransitive
      (Subgroup.closure (Set.range fun j : Fin 2 => titsDStar j)) (Fin 2925) := by
    rw [MulAction.isPretransitive_iff_base (0 : Fin 2925)]
    intro x
    obtain ⟨g, hg⟩ := titsDLine_transitive x
    exact ⟨⟨titsDLineAct g, titsDLineAct_range ▸ ⟨g, rfl⟩⟩, hg⟩
  have hHP : titsNLine.range ≤ Subgroup.closure (Set.range fun j : Fin 2 => titsDStar j) := by
    rw [← titsDLineAct_range]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  refine stabilizer_orbit_merge_primitivity (fun j : Fin 2 => titsDStar j) 0 titsNLine.range hHP
    (by rintro _ ⟨g, rfl⟩; exact titsNLine_fix g)
    (xs := fun j : Fin 5 => finPt 2925 titsOtherReps[(j : ℕ) + 1]!) ?_
    (fun j => ⟨titsOtherMerge j, ?_⟩)
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := titsNLine_orbit_cover x
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨⟨h, ⟨g, rfl⟩⟩, rfl⟩ := hxc
      apply hx
      show titsNLine g (finPt 2925 titsOtherReps[0]!) = 0
      rw [titsPrim_check.2.2.2.2.2.2.2.1]
      exact titsNLine_fix g
    obtain ⟨⟨h, hh⟩, e⟩ := hxc
    refine ⟨⟨c - 1, by omega⟩, h, hh, ?_⟩
    rw [← e]
    show h _ = h _
    congr 2
    rw [show c - 1 + 1 = c by omega]
  · have h := (titsPrim_check.2.2.2.2.2.2.2.2.2.2.2.2 j j.2).2
    have hx : ((finPt 2925 titsOtherReps[(j : ℕ) + 1]! : Fin 2925) : ℕ) =
        titsOtherReps[(j : ℕ) + 1]! := by
      apply finPt_val
      rw [titsPrim_check.2.2.2.2.2.2.2.1]
      fin_cases j <;> decide
    refine validInvariantMerge_of_mergeOK titsDStarArrs_rep ?_
    rw [hx]
    exact h

theorem AT_Tits_other_parabolic_primitivity :
    titsOtherReps = [0, 1, 7, 27, 107, 141] ∧ titsOtherSizes = [1, 12, 96, 768, 1024, 1024] ∧
    (∀ c < 6, (MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!)).ncard =
        titsOtherSizes[c]! ∧
      ∀ x ∈ MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!),
        titsOtherReps[c]! ≤ (x : ℕ)) ∧
    (∀ x : Fin 2925, ∃ c < 6, x ∈ MulAction.orbit titsNLine.range (finPt 2925 titsOtherReps[c]!)) ∧
    (∀ l < 5, (titsOtherMerge l).length = 2923 ∧
      ValidInvariantMerge (fun j : Fin 2 => titsDStar j) 0 (finPt 2925 titsOtherReps[l + 1]!)
        (titsOtherMerge l)) ∧
    titsDLineAct.range = Subgroup.closure (Set.range fun j : Fin 2 => titsDStar j) ∧
    MulAction.IsPreprimitive titsDLineAct.range (Fin 2925) := by
  refine ⟨titsPrim_check.2.2.2.2.2.2.2.1, titsPrim_check.2.2.2.2.2.2.2.2.1,
    fun c hc => ⟨titsNLine_orbit_ncard hc, titsNLine_orbit_least hc⟩, titsNLine_orbit_cover,
    fun l hl => ⟨(titsPrim_check.2.2.2.2.2.2.2.2.2.2.2.2 l hl).1, ?_⟩, titsDLineAct_range, ?_⟩
  · have h := (titsPrim_check.2.2.2.2.2.2.2.2.2.2.2.2 l hl).2
    have hx : ((finPt 2925 titsOtherReps[l + 1]! : Fin 2925) : ℕ) = titsOtherReps[l + 1]! := by
      apply finPt_val
      rw [titsPrim_check.2.2.2.2.2.2.2.1]
      interval_cases l <;> decide
    refine validInvariantMerge_of_mergeOK titsDStarArrs_rep ?_
    rw [hx]
    exact h
  · rw [titsDLineAct_range]
    exact titsDLine_primitive

end CFSG.Sporadic.Schreier.Tits
