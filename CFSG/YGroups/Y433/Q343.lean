module

public import CFSG.YGroups.Y433.Relabel

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

abbrev Y343 : Type := YGroup 3 4 3

namespace Y343

@[expose] def armStart : ℕ → ℕ
  | 1 => 1
  | 2 => 4
  | 3 => 8
  | _ => 0

@[expose] noncomputable def A : Y343 := yGen 3 4 3 0

@[expose] noncomputable def B (i : ℕ) : Y343 := yGen 3 4 3 (armStart i)

@[expose] noncomputable def C (i : ℕ) : Y343 := yGen 3 4 3 (armStart i + 1)

@[expose] noncomputable def D (i : ℕ) : Y343 := yGen 3 4 3 (armStart i + 2)

@[expose] noncomputable def E₂ : Y343 := yGen 3 4 3 (armStart 2 + 3)

@[expose] noncomputable def T (i : ℕ) : Y343 := A * B i * C i

@[expose] noncomputable def F (i j k : ℕ) : Y343 := (A * B i * C i * D i * B j * C j * B k) ^ 9

theorem yEdges_343 : yEdges 3 4 3 =
    [(0, armStart 1), (0, armStart 2), (0, armStart 3),
      (armStart 1, armStart 1 + 1), (armStart 1 + 1, armStart 1 + 2),
      (armStart 2, armStart 2 + 1), (armStart 2 + 1, armStart 2 + 2),
      (armStart 2 + 2, armStart 2 + 3),
      (armStart 3, armStart 3 + 1), (armStart 3 + 1, armStart 3 + 2)] := by
  decide

theorem spiderWord_343 : spiderWord 3 4 =
    [0, armStart 1, armStart 1 + 1, 0, armStart 2, armStart 2 + 1, 0, armStart 3,
      armStart 3 + 1] := by
  decide

theorem spider : (T 1 * T 2 * T 3) ^ 10 = 1 := by
  have h := evalWord_yGen_of_mem (p := 3) (q := 4) (r := 3)
    (w := (List.replicate 10 (spiderWord 3 4)).flatten) (by
      simp only [yRels, List.mem_append]
      refine Or.inr ?_
      simp)
  rw [Y443.evalWord_replicate_flatten] at h
  rw [← h, Relabel.evalWord_spiderWord]
  rfl

end Y343

@[expose] noncomputable def Q343Extra : Y343 := Y343.F 3 1 2

theorem Q343Extra_eq_evalWord :
    Q343Extra = evalWord (yGen 3 4 3) [0, 8, 9, 10, 1, 2, 4] ^ 9 := by
  simp only [Q343Extra, Y343.F, Y343.A, Y343.B, Y343.C, Y343.D, Y343.armStart, evalWord_cons,
    evalWord_nil, mul_one, mul_assoc, Nat.reduceAdd]

abbrev Q343 : Type := Y343 ⧸ Subgroup.normalClosure {Q343Extra}

@[expose] def delE1 (c : ℕ) : ℕ := if c < 4 then c else c - 1

theorem yRels_343_eq :
    yRels 3 4 3 = ((yRels 4 4 3).filter (fun w => decide (4 ∉ w))).map (List.map delE1) := by
  decide +kernel

theorem Q343Extra_letters :
    Q343Extra = evalWord (yGen 3 4 3) ([0, 9, 10, 11, 1, 2, 5].map delE1) ^ 9 :=
  Q343Extra_eq_evalWord

namespace Q343

@[expose] noncomputable def π : Y343 →* Q343 :=
  QuotientGroup.mk' (Subgroup.normalClosure {Q343Extra})

@[expose] noncomputable def vA : Q343 := π Y343.A

@[expose] noncomputable def vB (i : ℕ) : Q343 := π (Y343.B i)

@[expose] noncomputable def vC (i : ℕ) : Q343 := π (Y343.C i)

@[expose] noncomputable def vD (i : ℕ) : Q343 := π (Y343.D i)

@[expose] noncomputable def vE₂ : Q343 := π Y343.E₂

theorem π_surjective : Function.Surjective π := QuotientGroup.mk'_surjective _

theorem π_Q343Extra : π Q343Extra = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure rfl)

theorem ker_π : π.ker = Subgroup.normalClosure {Q343Extra} := QuotientGroup.ker_mk' _

noncomputable def lift {G : Type*} [Group G] (img : ℕ → G)
    (h : ∀ w ∈ yRels 3 4 3, evalWord img w = 1)
    (hextra : evalWord img [0, 8, 9, 10, 1, 2, 4] ^ 9 = 1) : Q343 →* G :=
  QuotientGroup.lift _ (yModelHom img h) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Q343Extra_eq_evalWord, map_pow,
      Relabel.yModelHom_evalWord _ (by decide)]
    exact hextra)

theorem lift_π {G : Type*} [Group G] (img : ℕ → G) (h : ∀ w ∈ yRels 3 4 3, evalWord img w = 1)
    (hextra : evalWord img [0, 8, 9, 10, 1, 2, 4] ^ 9 = 1) {c : ℕ} (hc : c < 11) :
    lift img h hextra (π (yGen 3 4 3 c)) = img c :=
  (QuotientGroup.lift_mk _ _ _).trans (yModelHom_yGen hc)

end Q343

@[expose] def Q343ExtraWord : List ℕ := (List.replicate 9 [0, 8, 9, 10, 1, 2, 4]).flatten

theorem Q343Extra_eq_evalWord_extraWord : Q343Extra = evalWord (yGen 3 4 3) Q343ExtraWord := by
  rw [Q343Extra_eq_evalWord, Q343ExtraWord, Y443.evalWord_replicate_flatten]

abbrev Q343Presented : Type :=
  PresentedGroup (yRelSet 3 4 3 ∪ {wordFG (ngen 3 4 3) Q343ExtraWord})

namespace Q343Presented

theorem lift_eq_comp_mk {α : Type*} {rels : Set (FreeGroup α)} {G : Type*} [Group G]
    (φ : PresentedGroup rels →* G) :
    FreeGroup.lift (fun c => φ (PresentedGroup.of c)) = φ.comp (PresentedGroup.mk rels) :=
  FreeGroup.ext_hom _ _ fun c => by simp [PresentedGroup.of]

theorem lift_of_eq_mk {rels : Set (FreeGroup (Fin (ngen 3 4 3)))}
    (r : FreeGroup (Fin (ngen 3 4 3))) :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) r = PresentedGroup.mk rels r := by
  have : FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]

theorem mk_extraWord :
    (PresentedGroup.mk (yRelSet 3 4 3) (wordFG (ngen 3 4 3) Q343ExtraWord) : Y343) =
      Q343Extra := by
  rw [Q343Extra_eq_evalWord_extraWord, evalWord_yGen]

noncomputable def toQ343 : Q343Presented →* Q343 :=
  PresentedGroup.toGroup (f := fun c => Q343.π (PresentedGroup.of c)) (by
    rw [lift_eq_comp_mk (Q343.π : Y343 →* Q343)]
    rintro r (hr | hr)
    · rw [MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
    · rw [Set.mem_singleton_iff.1 hr, MonoidHom.comp_apply, mk_extraWord, Q343.π_Q343Extra])

noncomputable def ofY343 : Y343 →* Q343Presented :=
  PresentedGroup.toGroup (f := PresentedGroup.of) (by
    intro r hr
    rw [lift_of_eq_mk]
    exact PresentedGroup.one_of_mem (Or.inl hr))

theorem ofY343_mk (x : FreeGroup (Fin (ngen 3 4 3))) :
    ofY343 (PresentedGroup.mk (yRelSet 3 4 3) x) =
      PresentedGroup.mk (yRelSet 3 4 3 ∪ {wordFG (ngen 3 4 3) Q343ExtraWord}) x :=
  (show FreeGroup.lift PresentedGroup.of x = _ from rfl).trans (lift_of_eq_mk x)

theorem ofY343_extra : ofY343 Q343Extra = 1 := by
  rw [← mk_extraWord, ofY343_mk]
  exact PresentedGroup.one_of_mem (Or.inr rfl)

noncomputable def ofQ343 : Q343 →* Q343Presented :=
  QuotientGroup.lift _ ofY343 (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ rfl
    exact ofY343_extra)

end Q343Presented

noncomputable def Q343EquivPresented : Q343 ≃* Q343Presented :=
  MonoidHom.toMulEquiv Q343Presented.ofQ343 Q343Presented.toQ343
    (by
      refine QuotientGroup.monoidHom_ext _ ?_
      refine PresentedGroup.ext fun c => ?_
      simp [Q343Presented.ofQ343, Q343Presented.ofY343, Q343Presented.toQ343, Q343.π])
    (by
      refine PresentedGroup.ext fun c => ?_
      simp [Q343Presented.ofQ343, Q343Presented.ofY343, Q343Presented.toQ343, Q343.π])

end CFSG.YGroups
