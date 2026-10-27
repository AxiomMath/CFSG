module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYPsi
public import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement

section Word

variable
    {F : Type} [Field F]

theorem rootD_height_pos : ∀ j : Fin 8, 0 < height (C2E6Std.rootD j) := by
  decide

theorem rootD_ne_neg (j j' : Fin 8) : C2E6Std.rootD j ≠ -C2E6Std.rootD j' := by
  intro h
  have h0 := (C2E6Std.rootD_zero_five j).1
  rw [h, Pi.neg_apply, (C2E6Std.rootD_zero_five j').1] at h0
  norm_num at h0

theorem rootD_add_not_mem_rootFinset :
    ∀ j j' : Fin 8, j ≠ j' → C2E6Std.rootD j + C2E6Std.rootD j' ∉ rootFinset Tag.E6 := by
  decide +kernel

theorem rootD_add_not_isRoot {j j' : Fin 8} (h : j ≠ j') :
    ¬ IsRoot Tag.E6 (C2E6Std.rootD j + C2E6Std.rootD j') := by
  rw [← mem_rootFinset]
  exact rootD_add_not_mem_rootFinset j j' h

theorem pinnedX_rootD_commute_self (j : Fin 8) (c d : F) :
    Commute (pinnedX Tag.E6 F (C2E6Std.rootD j) c)
      (pinnedX Tag.E6 F (C2E6Std.rootD j) d) := by
  rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]

theorem pinnedX_rootD_commute {j j' : Fin 8} (h : j ≠ j') (c d : F) :
    Commute (pinnedX Tag.E6 F (C2E6Std.rootD j) c)
      (pinnedX Tag.E6 F (C2E6Std.rootD j') d) := by
  have hne : C2E6Std.rootD j ≠ C2E6Std.rootD j' := fun hh => h (C2E6Std.rootD_injective hh)
  exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (α := C2E6Std.rootD j) (β := C2E6Std.rootD j')
    (C2E6Std.isRoot_rootD j) (C2E6Std.isRoot_rootD j') hne (rootD_ne_neg j j')).2
    (rootD_add_not_isRoot h) F _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

private noncomputable def d4WordGroup : Subgroup (ModGL Tag.E6 F) :=
  Subgroup.closure (Set.range fun p : Fin 8 × F =>
    pinnedX Tag.E6 F (C2E6Std.rootD p.1) p.2)

private theorem d4WordGroup_pairwise :
    (Set.range fun p : Fin 8 × F =>
      pinnedX Tag.E6 F (C2E6Std.rootD p.1) p.2).Pairwise Commute := by
  rintro _ ⟨⟨j, c⟩, rfl⟩ _ ⟨⟨j', d⟩, rfl⟩ _
  by_cases h : j = j'
  · subst h
    exact pinnedX_rootD_commute_self j c d
  · exact pinnedX_rootD_commute h c d

private noncomputable instance d4WordGroup_commGroup : CommGroup (d4WordGroup (F := F)) :=
  Subgroup.closureCommGroupOfComm d4WordGroup_pairwise

private noncomputable def d4WordGen (j : Fin 8) (c : F) : d4WordGroup (F := F) :=
  ⟨pinnedX Tag.E6 F (C2E6Std.rootD j) c, Subgroup.subset_closure ⟨(j, c), rfl⟩⟩

private theorem d4WordGen_add (j : Fin 8) (c d : F) :
    d4WordGen (F := F) j (c + d) =
      d4WordGen (F := F) j c * d4WordGen (F := F) j d :=
  Subtype.ext (pinnedX_add Tag.E6 F (C2E6Std.rootD j) c d)

private theorem d4WordGen_zero (j : Fin 8) : d4WordGen (F := F) j 0 = 1 :=
  Subtype.ext (pinnedX_zero Tag.E6 F (C2E6Std.rootD j))

private noncomputable def d4WordZ (a : Fin 8 → F) : d4WordGroup (F := F) :=
  ∏ j : Fin 8, d4WordGen (F := F) j (a j)

private theorem d4WordZ_add (a b : Fin 8 → F) :
    d4WordZ (a + b) = d4WordZ a * d4WordZ b := by
  simp only [d4WordZ, Pi.add_apply, d4WordGen_add]
  exact Finset.prod_mul_distrib

private noncomputable def d4RootWordFin (a : Fin 8 → F) : ModGL Tag.E6 F :=
  (List.ofFn fun j : Fin 8 => pinnedX Tag.E6 F (C2E6Std.rootD j) (a j)).prod

private theorem coe_d4WordZ (a : Fin 8 → F) :
    (d4WordZ a : ModGL Tag.E6 F) = d4RootWordFin a := by
  have hcoe : ((∏ j : Fin 8, d4WordGen j (a j) : d4WordGroup) : ModGL Tag.E6 F) =
      (List.ofFn fun j : Fin 8 => pinnedX Tag.E6 F (C2E6Std.rootD j) (a j)).prod := by
    rw [← Fin.prod_ofFn (fun j : Fin 8 => d4WordGen j (a j))]
    refine (SubmonoidClass.coe_list_prod
      (List.ofFn fun j : Fin 8 => d4WordGen j (a j))).trans ?_
    rw [← List.ofFn_comp' (fun j : Fin 8 => d4WordGen j (a j))
      (fun x : d4WordGroup => (x : ModGL Tag.E6 F))]
    exact congrArg List.prod (congrArg List.ofFn (funext fun j => rfl))
  rw [d4WordZ]
  exact hcoe

noncomputable def d4RootWord (z : Fin 4 ⊕ Fin 4 → F) : ModGL Tag.E6 F :=
  (List.ofFn fun j : Fin 8 => pinnedX Tag.E6 F (C2E6Std.rootD j) (z (C2E6Std.natD j))).prod

private theorem d4RootWord_eq_fin (z : Fin 4 ⊕ Fin 4 → F) :
    d4RootWord z = d4RootWordFin (fun j => z (C2E6Std.natD j)) :=
  rfl

private theorem coe_d4WordZ_natD (z : Fin 4 ⊕ Fin 4 → F) :
    (d4WordZ (fun j => z (C2E6Std.natD j)) : ModGL Tag.E6 F) = d4RootWord z :=
  (coe_d4WordZ _).trans (d4RootWord_eq_fin z).symm

theorem d4RootWord_add (z₁ z₂ : Fin 4 ⊕ Fin 4 → F) :
    d4RootWord (z₁ + z₂) = d4RootWord z₁ * d4RootWord z₂ := by
  rw [← coe_d4WordZ_natD (z₁ + z₂), ← coe_d4WordZ_natD z₁,
    ← coe_d4WordZ_natD z₂]
  have h : (fun j : Fin 8 => (z₁ + z₂) (C2E6Std.natD j)) =
      (fun j : Fin 8 => z₁ (C2E6Std.natD j)) +
        (fun j : Fin 8 => z₂ (C2E6Std.natD j)) := rfl
  rw [h, d4WordZ_add, Subgroup.coe_mul]

theorem d4RootWord_zero : d4RootWord (0 : Fin 4 ⊕ Fin 4 → F) = 1 := by
  rw [← coe_d4WordZ_natD (0 : Fin 4 ⊕ Fin 4 → F)]
  have h : (fun j : Fin 8 => (0 : Fin 4 ⊕ Fin 4 → F) (C2E6Std.natD j)) =
      (0 : Fin 8 → F) := rfl
  rw [h]
  have hz : d4WordZ (0 : Fin 8 → F) = 1 := by
    rw [d4WordZ]
    exact Finset.prod_eq_one (fun j _ => d4WordGen_zero (F := F) j)
  rw [hz]
  rfl

theorem d4RootWord_single (j : Fin 8) (d : F) :
    d4RootWord (Pi.single (C2E6Std.natD j) d) =
      pinnedX Tag.E6 F (C2E6Std.rootD j) d := by
  rw [← coe_d4WordZ_natD (Pi.single (C2E6Std.natD j) d)]
  have hcomp : (fun k : Fin 8 =>
        (Pi.single (C2E6Std.natD j) d : Fin 4 ⊕ Fin 4 → F) (C2E6Std.natD k)) =
      (Pi.single j d : Fin 8 → F) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · have hne : C2E6Std.natD k ≠ C2E6Std.natD j :=
        fun hh => hk (C2E6Std.natD_injective hh)
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hk]
  rw [hcomp]
  have hz : d4WordZ (Pi.single j d : Fin 8 → F) = d4WordGen (F := F) j d := by
    rw [d4WordZ, Finset.prod_eq_single j]
    · rw [Pi.single_eq_same]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk]
      exact d4WordGen_zero (F := F) k
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hz]
  rfl

private theorem sum_single_natD (z : Fin 4 ⊕ Fin 4 → F) :
    (∑ j : Fin 8, Pi.single (C2E6Std.natD j) (z (C2E6Std.natD j))) = z := by
  funext s
  obtain ⟨j, rfl⟩ := C2E6Std.exists_natD_eq s
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    have hne : C2E6Std.natD k ≠ C2E6Std.natD j :=
      fun hh => hk (C2E6Std.natD_injective hh)
    rw [Pi.single_eq_of_ne (Ne.symm hne)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem d4RootWord_injective : Function.Injective (d4RootWord (F := F)) := by
  intro z₁ z₂ h
  have h' := (positive_root_product_injectivity Tag.E6 F
    (C2E6Std.rootD : Fin 8 → Fin Tag.E6.rank → ℤ) C2E6Std.rootD_injective
    (fun j => ⟨C2E6Std.isRoot_rootD j, rootD_height_pos j⟩)).2 h
  funext s
  obtain ⟨j, rfl⟩ := C2E6Std.exists_natD_eq s
  exact congrFun h' j

end Word

section CharTwo

variable
    {F : Type} [Field F] [CharP F 2]

private theorem smul_single_one (s : Fin 4 ⊕ Fin 4) (c : F) :
    c • (Pi.single s (1 : F) : Fin 4 ⊕ Fin 4 → F) = Pi.single s c := by
  funext x
  by_cases h : x = s
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

private theorem d4ElementaryMap_single_charTwo_smul {p q : Fin 4 ⊕ Fin 4}
    (hpq : p.swap ≠ q.swap) (c d : F) (s : Fin 4 ⊕ Fin 4) :
    orthElementaryMap (quadPlus 4 F) (Pi.single p 1) ((-c) • Pi.single q 1)
        (Pi.single s d) =
      Pi.single s d + (if s = p.swap then (c * d) • Pi.single q 1
        else if s = q.swap then (c * d) • Pi.single p 1 else 0) := by
  have hsmul : (Pi.single s d : Fin 4 ⊕ Fin 4 → F) = d • Pi.single s (1 : F) := by
    funext x
    by_cases hx : x = s
    · subst hx; simp
    · simp [Pi.single_eq_of_ne hx]
  rw [hsmul, map_smul, d4ElementaryMap_single_charTwo hpq]
  rw [smul_add]
  congr 1
  by_cases h1 : s = p.swap
  · rw [if_pos h1, if_pos h1, smul_smul, mul_comm]
  · by_cases h2 : s = q.swap
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, smul_smul, mul_comm]
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, smul_zero]

private theorem d4Psi_xUnit_single (k : Fin 4) (c d : F) (j : Fin 8) :
    d4Psi F ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) =
      Pi.single (C2E6Std.natD j) d +
        (if C2E6Std.natD j = (posCenter k).swap then
            (c * d) • Pi.single (posParam k) 1
          else if C2E6Std.natD j = (posParam k).swap then
            (c * d) • Pi.single (posCenter k) 1 else 0) := by
  rw [d4Psi_xUnit]
  change (rootElt 4 F (OrthogonalSplit.simpleRoot 4 k) c).toLinearMap
      (Pi.single (C2E6Std.natD j) d) = _
  rw [d4RootElt_simpleRoot]
  exact d4ElementaryMap_single_charTwo_smul (center_param_ne k).1 c d _

private theorem d4Psi_yUnit_single (k : Fin 4) (c d : F) (j : Fin 8) :
    d4Psi F ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) =
      Pi.single (C2E6Std.natD j) d +
        (if C2E6Std.natD j = (negCenter k).swap then
            (c * d) • Pi.single (negParam k) 1
          else if C2E6Std.natD j = (negParam k).swap then
            (c * d) • Pi.single (negCenter k) 1 else 0) := by
  rw [d4Psi_yUnit]
  change (rootElt 4 F (-OrthogonalSplit.simpleRoot 4 k) c).toLinearMap
      (Pi.single (C2E6Std.natD j) d) = _
  rw [d4RootElt_neg_simpleRoot]
  exact d4ElementaryMap_single_charTwo_smul (center_param_ne k).2 c d _

private theorem d4Psi_xUnit_single_raise (k : Fin 4) (c d : F) {j j' : Fin 8}
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :
    d4Psi F ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) =
      Pi.single (C2E6Std.natD j) d + Pi.single (C2E6Std.natD j') (c * d) := by
  rw [d4Psi_xUnit_single]
  rcases C2E6Std.raise_natD j j' k hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h2, smul_single_one]
  · rw [if_neg, if_pos h1, h2, smul_single_one]
    intro h
    exact (center_param_ne k).1 (h1.symm.trans h).symm

private theorem d4Psi_xUnit_single_noroot (k : Fin 4) (c d : F) (j : Fin 8)
    (h : ¬ IsRoot Tag.E6 (C2E6Std.rootD j + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))) :
    d4Psi F ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) = Pi.single (C2E6Std.natD j) d := by
  rw [d4Psi_xUnit_single]
  have hno : ¬ (C2E6Std.natD j = (posCenter k).swap ∨
      C2E6Std.natD j = (posParam k).swap) := by
    intro hs
    obtain ⟨j', hj'⟩ := (C2E6Std.raise_rootD j k).2 hs
    exact h (hj' ▸ C2E6Std.isRoot_rootD j')
  rw [if_neg (fun h1 => hno (Or.inl h1)), if_neg (fun h2 => hno (Or.inr h2)), add_zero]

private theorem d4Psi_yUnit_single_lower (k : Fin 4) (c d : F) {j j' : Fin 8}
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j - (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :
    d4Psi F ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) =
      Pi.single (C2E6Std.natD j) d + Pi.single (C2E6Std.natD j') (c * d) := by
  rw [d4Psi_yUnit_single]
  rcases C2E6Std.lower_natD j j' k hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h2, smul_single_one]
  · rw [if_neg, if_pos h1, h2, smul_single_one]
    intro h
    exact (center_param_ne k).2 (h1.symm.trans h).symm

private theorem d4Psi_yUnit_single_noroot (k : Fin 4) (c d : F) (j : Fin 8)
    (h : ¬ IsRoot Tag.E6 (C2E6Std.rootD j - (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))) :
    d4Psi F ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d) = Pi.single (C2E6Std.natD j) d := by
  rw [d4Psi_yUnit_single]
  have hno : ¬ (C2E6Std.natD j = (negCenter k).swap ∨
      C2E6Std.natD j = (negParam k).swap) := by
    intro hs
    obtain ⟨j', hj'⟩ := (C2E6Std.lower_rootD j k).2 hs
    exact h (hj' ▸ C2E6Std.isRoot_rootD j')
  rw [if_neg (fun h1 => hno (Or.inl h1)), if_neg (fun h2 => hno (Or.inr h2)), add_zero]

private theorem rootD_ne_raised {k : Fin 4} {j j' : Fin 8}
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) : j ≠ j' := by
  intro h
  subst h
  have h0 : ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ) = 0 := by
    have h := congrArg (fun v : Fin Tag.E6.rank → ℤ => v - C2E6Std.rootD j) hj'.symm
    simpa using h
  have h1 := congrFun h0 (C2E6Std.jD k)
  simp at h1

private theorem rootD_ne_lowered {k : Fin 4} {j j' : Fin 8}
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j - (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) : j ≠ j' := by
  intro h
  subst h
  have h0 : ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ) = 0 := by
    have h := congrArg (fun v : Fin Tag.E6.rank → ℤ => v + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) hj'.symm
    simpa using h
  have h1 := congrFun h0 (C2E6Std.jD k)
  simp at h1

private theorem conj_xUnit_raise (k : Fin 4) (j j' : Fin 8) (c d : F)
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :
    xUnit Tag.E6 F (C2E6Std.jD k) c * pinnedX Tag.E6 F (C2E6Std.rootD j) d *
        (xUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      pinnedX Tag.E6 F (C2E6Std.rootD j') (c * d) *
        pinnedX Tag.E6 F (C2E6Std.rootD j) d := by
  rw [← pinnedX_single (τ := Tag.E6) (R := F) (i := C2E6Std.jD k) c]
  have hγ : IsRoot Tag.E6 ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) := isRoot_single Tag.E6 (C2E6Std.jD k)
  have hδ : IsRoot Tag.E6 (C2E6Std.rootD j) := C2E6Std.isRoot_rootD j
  have hne : (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ C2E6Std.rootD j :=
    (C2E6Std.rootD_ne_single j k).1.symm
  have hne' : (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ -C2E6Std.rootD j := by
    intro hh
    exact (C2E6Std.rootD_ne_single j k).2 (by
      have := congrArg Neg.neg hh
      simpa using this.symm)
  have hδ' : IsRoot Tag.E6 ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j) := by
    rw [add_comm, ← hj']
    exact C2E6Std.isRoot_rootD j'
  have hcomm' : ⁅pinnedX Tag.E6 F ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) c,
      pinnedX Tag.E6 F (C2E6Std.rootD j) d⁆ =
      pinnedX Tag.E6 F (C2E6Std.rootD j') (c * d) := by
    have hsum : (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j =
        C2E6Std.rootD j' := by
      rw [add_comm, hj']
    obtain ⟨hε, hformula⟩ :=
      (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
        (α := (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))
        (β := C2E6Std.rootD j) hγ hδ hne hne').1 hδ'
    have hcoef : ((commConst Tag.E6
        (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)
        (C2E6Std.rootD j) (1, 1) : ℤ) : F) = 1 := by
      rcases hε with hε | hε
      · rw [hε]; norm_num
      · rw [hε, Int.cast_neg, Int.cast_one]
        exact CharTwo.neg_eq 1
    have h := hformula F c d
    rw [hcoef, one_mul, hsum] at h
    exact h
  rw [← hcomm', commutatorElement_def]
  group

private theorem conj_xUnit_commute (k : Fin 4) (j : Fin 8) (c d : F)
    (h : ¬ IsRoot Tag.E6 (C2E6Std.rootD j + (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))) :
    xUnit Tag.E6 F (C2E6Std.jD k) c * pinnedX Tag.E6 F (C2E6Std.rootD j) d *
        (xUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      pinnedX Tag.E6 F (C2E6Std.rootD j) d := by
  rw [← pinnedX_single (τ := Tag.E6) (R := F) (i := C2E6Std.jD k) c]
  have hγ : IsRoot Tag.E6 ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) := isRoot_single Tag.E6 (C2E6Std.jD k)
  have hδ : IsRoot Tag.E6 (C2E6Std.rootD j) := C2E6Std.isRoot_rootD j
  have hne : (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ C2E6Std.rootD j :=
    (C2E6Std.rootD_ne_single j k).1.symm
  have hne' : (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ -C2E6Std.rootD j := by
    intro hh
    exact (C2E6Std.rootD_ne_single j k).2 (by
      have := congrArg Neg.neg hh
      simpa using this.symm)
  have hnr : ¬ IsRoot Tag.E6 ((Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j) := by
    rwa [add_comm]
  have hc := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (α := (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))
    (β := C2E6Std.rootD j) hγ hδ hne hne').2 hnr F _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  rw [hc.eq]
  group

private theorem conj_yUnit_lower (k : Fin 4) (j j' : Fin 8) (c d : F)
    (hj' : C2E6Std.rootD j' = C2E6Std.rootD j - (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :
    yUnit Tag.E6 F (C2E6Std.jD k) c * pinnedX Tag.E6 F (C2E6Std.rootD j) d *
        (yUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      pinnedX Tag.E6 F (C2E6Std.rootD j') (c * d) *
        pinnedX Tag.E6 F (C2E6Std.rootD j) d := by
  rw [← pinnedX_neg_single (τ := Tag.E6) (R := F) (i := C2E6Std.jD k) c]
  have hγ : IsRoot Tag.E6 (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :=
    isRoot_neg_single Tag.E6 (C2E6Std.jD k)
  have hδ : IsRoot Tag.E6 (C2E6Std.rootD j) := C2E6Std.isRoot_rootD j
  have hne : -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ C2E6Std.rootD j :=
    (C2E6Std.rootD_ne_single j k).2.symm
  have hne' : -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ -C2E6Std.rootD j := by
    intro hh
    exact (C2E6Std.rootD_ne_single j k).1 (by
      have := congrArg Neg.neg hh
      simpa using this.symm)
  have hδ' : IsRoot Tag.E6 (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j) := by
    rw [add_comm, ← sub_eq_add_neg, ← hj']
    exact C2E6Std.isRoot_rootD j'
  have hcomm' : ⁅pinnedX Tag.E6 F (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) c,
      pinnedX Tag.E6 F (C2E6Std.rootD j) d⁆ =
      pinnedX Tag.E6 F (C2E6Std.rootD j') (c * d) := by
    have hsum : -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j =
        C2E6Std.rootD j' := by
      rw [add_comm, ← sub_eq_add_neg, hj']
    obtain ⟨hε, hformula⟩ :=
      (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
        (α := -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))
        (β := C2E6Std.rootD j) hγ hδ hne hne').1 hδ'
    have hcoef : ((commConst Tag.E6
        (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))
        (C2E6Std.rootD j) (1, 1) : ℤ) : F) = 1 := by
      rcases hε with hε | hε
      · rw [hε]; norm_num
      · rw [hε, Int.cast_neg, Int.cast_one]
        exact CharTwo.neg_eq 1
    have h := hformula F c d
    rw [hcoef, one_mul, hsum] at h
    exact h
  rw [← hcomm', commutatorElement_def]
  group

private theorem conj_yUnit_commute (k : Fin 4) (j : Fin 8) (c d : F)
    (h : ¬ IsRoot Tag.E6 (C2E6Std.rootD j - (Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))) :
    yUnit Tag.E6 F (C2E6Std.jD k) c * pinnedX Tag.E6 F (C2E6Std.rootD j) d *
        (yUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      pinnedX Tag.E6 F (C2E6Std.rootD j) d := by
  rw [← pinnedX_neg_single (τ := Tag.E6) (R := F) (i := C2E6Std.jD k) c]
  have hγ : IsRoot Tag.E6 (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ)) :=
    isRoot_neg_single Tag.E6 (C2E6Std.jD k)
  have hδ : IsRoot Tag.E6 (C2E6Std.rootD j) := C2E6Std.isRoot_rootD j
  have hne : -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ C2E6Std.rootD j :=
    (C2E6Std.rootD_ne_single j k).2.symm
  have hne' : -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) ≠ -C2E6Std.rootD j := by
    intro hh
    exact (C2E6Std.rootD_ne_single j k).1 (by
      have := congrArg Neg.neg hh
      simpa using this.symm)
  have hnr : ¬ IsRoot Tag.E6 (-(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ) + C2E6Std.rootD j) := by
    simpa [sub_eq_add_neg, add_comm] using h
  have hc := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl))
    (α := -(Pi.single (C2E6Std.jD k) (1 : ℤ) : Fin Tag.E6.rank → ℤ))
    (β := C2E6Std.rootD j) hγ hδ hne hne').2 hnr F _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  rw [hc.eq]
  group

private theorem d4Psi_conj_rootD_single_xUnit (k : Fin 4) (c d : F) (j : Fin 8) :
    xUnit Tag.E6 F (C2E6Std.jD k) c *
        d4RootWord (Pi.single (C2E6Std.natD j) d) *
        (xUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      d4RootWord (d4Psi F ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d)) := by
  rw [d4RootWord_single]
  rcases C2E6Std.raiseD_or j k with ⟨j', hj'⟩ | h
  · rw [d4Psi_xUnit_single_raise k c d hj', d4RootWord_add,
      d4RootWord_single, d4RootWord_single, conj_xUnit_raise k j j' c d hj']
    exact (pinnedX_rootD_commute (j := j') (j' := j) (Ne.symm (rootD_ne_raised hj')) (c * d) d).eq
  · rw [d4Psi_xUnit_single_noroot k c d j h, d4RootWord_single,
      conj_xUnit_commute k j c d h]

private theorem d4Psi_conj_rootD_single_yUnit (k : Fin 4) (c d : F) (j : Fin 8) :
    yUnit Tag.E6 F (C2E6Std.jD k) c *
        d4RootWord (Pi.single (C2E6Std.natD j) d) *
        (yUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
      d4RootWord (d4Psi F ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩
        (Pi.single (C2E6Std.natD j) d)) := by
  rw [d4RootWord_single]
  rcases C2E6Std.lowerD_or j k with ⟨j', hj'⟩ | h
  · rw [d4Psi_yUnit_single_lower k c d hj', d4RootWord_add,
      d4RootWord_single, d4RootWord_single, conj_yUnit_lower k j j' c d hj']
    exact (pinnedX_rootD_commute (j := j') (j' := j) (Ne.symm (rootD_ne_lowered hj')) (c * d) d).eq
  · rw [d4Psi_yUnit_single_noroot k c d j h, d4RootWord_single,
      conj_yUnit_commute k j c d h]

private theorem d4Psi_add (g : d4Levi F) (z₁ z₂ : Fin 4 ⊕ Fin 4 → F) :
    d4Psi F g (z₁ + z₂) = d4Psi F g z₁ + d4Psi F g z₂ :=
  map_add (d4Psi F g) z₁ z₂

private def d4Good (g : ModGL Tag.E6 F) : Prop :=
  ∀ (hg : g ∈ d4Levi F) (z : Fin 4 ⊕ Fin 4 → F),
    g * d4RootWord z * g⁻¹ = d4RootWord (d4Psi F ⟨g, hg⟩ z)

private theorem d4Good_one : d4Good (1 : ModGL Tag.E6 F) := by
  intro hg z
  have hsub : (⟨1, hg⟩ : d4Levi F) = 1 := Subtype.ext rfl
  rw [hsub, map_one]
  simp

private theorem d4Good_mul {x y : ModGL Tag.E6 F} (hx : x ∈ d4Levi F)
    (hy : y ∈ d4Levi F) (hxg : d4Good x) (hyg : d4Good y) : d4Good (x * y) := by
  intro hxy z
  have h1 := hxg hx (d4Psi F ⟨y, hy⟩ z)
  have h2 := hyg hy z
  have hsub : (⟨x * y, hxy⟩ : d4Levi F) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
  calc (x * y) * d4RootWord z * (x * y)⁻¹
      = x * (y * d4RootWord z * y⁻¹) * x⁻¹ := by group
    _ = x * d4RootWord (d4Psi F ⟨y, hy⟩ z) * x⁻¹ := by rw [h2]
    _ = d4RootWord (d4Psi F ⟨x, hx⟩ (d4Psi F ⟨y, hy⟩ z)) := h1
    _ = d4RootWord (d4Psi F ⟨x * y, hxy⟩ z) := by
        rw [hsub, map_mul]
        rfl

private theorem d4Good_xUnit (k : Fin 4) (c : F) :
    d4Good (xUnit Tag.E6 F (C2E6Std.jD k) c) := by
  intro hg z
  have hsub : (⟨xUnit Tag.E6 F (C2E6Std.jD k) c, hg⟩ : d4Levi F) =
      ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩ := Subtype.ext rfl
  rw [hsub]
  have hsum : ∀ s : Finset (Fin 8),
      xUnit Tag.E6 F (C2E6Std.jD k) c *
          d4RootWord (∑ j ∈ s, Pi.single (C2E6Std.natD j) (z (C2E6Std.natD j))) *
          (xUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
        d4RootWord (d4Psi F
          ⟨xUnit Tag.E6 F (C2E6Std.jD k) c, xUnit_mem_d4Levi k c⟩
          (∑ j ∈ s, Pi.single (C2E6Std.natD j) (z (C2E6Std.natD j)))) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, d4RootWord_zero, map_zero, d4RootWord_zero]
        group
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, d4RootWord_add, d4Psi_add, d4RootWord_add]
        rw [← ih, ← d4Psi_conj_rootD_single_xUnit k c (z (C2E6Std.natD j)) j]
        group
  have hfin := hsum Finset.univ
  rwa [sum_single_natD z] at hfin

private theorem d4Good_yUnit (k : Fin 4) (c : F) :
    d4Good (yUnit Tag.E6 F (C2E6Std.jD k) c) := by
  intro hg z
  have hsub : (⟨yUnit Tag.E6 F (C2E6Std.jD k) c, hg⟩ : d4Levi F) =
      ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩ := Subtype.ext rfl
  rw [hsub]
  have hsum : ∀ s : Finset (Fin 8),
      yUnit Tag.E6 F (C2E6Std.jD k) c *
          d4RootWord (∑ j ∈ s, Pi.single (C2E6Std.natD j) (z (C2E6Std.natD j))) *
          (yUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
        d4RootWord (d4Psi F
          ⟨yUnit Tag.E6 F (C2E6Std.jD k) c, yUnit_mem_d4Levi k c⟩
          (∑ j ∈ s, Pi.single (C2E6Std.natD j) (z (C2E6Std.natD j)))) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, d4RootWord_zero, map_zero, d4RootWord_zero]
        group
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, d4RootWord_add, d4Psi_add, d4RootWord_add]
        rw [← ih, ← d4Psi_conj_rootD_single_yUnit k c (z (C2E6Std.natD j)) j]
        group
  have hfin := hsum Finset.univ
  rwa [sum_single_natD z] at hfin

private theorem d4Good_of_mem {g : ModGL Tag.E6 F} (hg : g ∈ d4Levi F) : d4Good g := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
      rcases hx with ⟨i, hi, c, rfl | rfl⟩
      · obtain ⟨k, rfl⟩ := C2E6Std.exists_jD_of_mem_setD hi
        exact d4Good_xUnit k c
      · obtain ⟨k, rfl⟩ := C2E6Std.exists_jD_of_mem_setD hi
        exact d4Good_yUnit k c
  | inv_mem x hx =>
      rcases hx with ⟨i, hi, c, rfl | rfl⟩
      · obtain ⟨k, rfl⟩ := C2E6Std.exists_jD_of_mem_setD hi
        rw [xUnit_inv (τ := Tag.E6) (C2E6Std.jD k) c]
        exact d4Good_xUnit k (-c)
      · obtain ⟨k, rfl⟩ := C2E6Std.exists_jD_of_mem_setD hi
        rw [show (yUnit Tag.E6 F (C2E6Std.jD k) c)⁻¹ =
          yUnit Tag.E6 F (C2E6Std.jD k) (-c) from
            Units.ext (coe_yUnit_inv (C2E6Std.jD k) c)]
        exact d4Good_yUnit k (-c)
  | one => exact d4Good_one
  | mul x y hx hy ihx ihy => exact d4Good_mul hx hy ihx ihy

theorem d4Psi_conj_rootD_product (g : d4Levi F) (z : Fin 4 ⊕ Fin 4 → F) :
    (g : ModGL Tag.E6 F) * d4RootWord z * (g : ModGL Tag.E6 F)⁻¹ =
      d4RootWord (d4Psi F g z) :=
  d4Good_of_mem g.2 g.2 z

end CharTwo

end CFSG.SeitzReduction.TwistedE6Pilot
