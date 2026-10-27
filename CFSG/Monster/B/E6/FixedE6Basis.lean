module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData

public noncomputable section

namespace CFSG.Monster.B.E6.FixedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K ω bar barHom)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev V : Type := RootModule Tag.E6 K

@[expose] def rhoE6 : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem cartan_rhoE6 (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (rhoE6 i) (rhoE6 j) = Tag.E6.cartan i j :=
  TwistTag.E6.cartan_perm i j

@[expose] def labelRho : Label Tag.E6 ≃ Label Tag.E6 := labelPerm rhoE6 cartan_rhoE6

abbrev PV : Module.End K V := (diagramMap TwistTag.E6 K).1

@[expose] def sqV (v : V) : V := Finsupp.mapRange barHom (map_zero barHom) v

@[expose] def fixedMap (v : V) : V := PV (sqV v)

theorem sqV_apply (v : V) (l : Label Tag.E6) : sqV v l = v l ^ 2 := rfl

theorem PV_apply (v : V) (l : Label Tag.E6) : PV v l = v (labelRho.symm l) := by
  change Finsupp.equivMapDomain labelRho v l = _
  rw [Finsupp.equivMapDomain_apply]

theorem rhoE6_rhoE6 (i : Fin Tag.E6.rank) : rhoE6 (rhoE6 i) = i := by
  fin_cases i <;> rfl

theorem rhoE6_symm (i : Fin Tag.E6.rank) : rhoE6.symm i = rhoE6 i := by
  rw [Equiv.symm_apply_eq, rhoE6_rhoE6]

theorem permLattice_permLattice (v : Fin Tag.E6.rank → ℤ) :
    permLattice rhoE6 (permLattice rhoE6 v) = v := by
  ext j
  simp only [permLattice, Function.comp_apply, rhoE6_symm, rhoE6_rhoE6]

theorem labelRho_inl (i : Fin Tag.E6.rank) : labelRho (Sum.inl i) = Sum.inl (rhoE6 i) := rfl

theorem labelRho_inr (α : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) :
    labelRho (Sum.inr α) = Sum.inr ⟨permLattice rhoE6 α.1, α.2.permLattice cartan_rhoE6⟩ := rfl

theorem labelRho_labelRho (l : Label Tag.E6) : labelRho (labelRho l) = l := by
  rcases l with i | α
  · rw [labelRho_inl, labelRho_inl, rhoE6_rhoE6]
  · rw [labelRho_inr, labelRho_inr]
    exact congrArg Sum.inr (Subtype.ext (permLattice_permLattice α.1))

theorem labelRho_symm (l : Label Tag.E6) : labelRho.symm l = labelRho l := by
  rw [Equiv.symm_apply_eq, labelRho_labelRho]

theorem fixedMap_apply (v : V) (l : Label Tag.E6) : fixedMap v l = v (labelRho l) ^ 2 := by
  rw [fixedMap, PV_apply, sqV_apply, labelRho_symm]

@[expose] def IsFirst (l : Label Tag.E6) : Prop := Label.Precedes l (labelRho l)

theorem isFirst_inl (i : Fin Tag.E6.rank) : IsFirst (Sum.inl i) ↔ i < rhoE6 i := by
  rw [IsFirst, labelRho_inl]
  simp [Label.Precedes, Label.weight]

theorem isFirst_inr
    (α : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) :
    IsFirst (Sum.inr α) ↔ toLex α.1 < toLex (permLattice rhoE6 α.1) := by
  rw [IsFirst, labelRho_inr]
  simp only [Label.Precedes, Label.weight, height_permLattice, lt_irrefl, false_or, true_and]

theorem isFirst_iff_not_isFirst
    {l : Label Tag.E6} (hl : labelRho l ≠ l) :
    IsFirst l ↔ ¬IsFirst (labelRho l) := by
  rcases l with i | α
  · have hne : rhoE6 i ≠ i := fun h => hl (by rw [labelRho_inl, h])
    rw [labelRho_inl, isFirst_inl, isFirst_inl, rhoE6_rhoE6]
    constructor
    · exact fun h h' => lt_asymm h h'
    · intro h
      rcases lt_trichotomy i (rhoE6 i) with h1 | h1 | h1
      · exact h1
      · exact absurd h1.symm hne
      · exact absurd h1 h
  · have hne : permLattice rhoE6 α.1 ≠ α.1 := fun h =>
      hl (by rw [labelRho_inr]; exact congrArg Sum.inr (Subtype.ext h))
    rw [labelRho_inr, isFirst_inr, isFirst_inr]
    simp only [permLattice_permLattice]
    constructor
    · exact fun h h' => lt_asymm h h'
    · intro h
      rcases lt_trichotomy (toLex α.1) (toLex (permLattice rhoE6 α.1)) with h1 | h1 | h1
      · exact h1
      · exact absurd (toLex.injective h1).symm hne
      · exact absurd h1 h

theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem omega_add_omega_sq : ω + ω ^ 2 = 1 := by
  linear_combination C2E6Overlap.omega_sq_add_omega_add_one - two_eq_zero_K

theorem omega_cube : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * C2E6Overlap.omega_sq_add_omega_add_one

open _root_.Classical in
@[expose] def basisVec (l : Label Tag.E6) : V :=
  if labelRho l = l then Finsupp.single l 1
  else if IsFirst l then Finsupp.single l 1 + Finsupp.single (labelRho l) 1
  else ω • Finsupp.single (labelRho l) 1 + ω ^ 2 • Finsupp.single l 1

open _root_.Classical in
@[expose] def coordK (v : V) (l : Label Tag.E6) : K :=
  if labelRho l = l then v l
  else if IsFirst l then v l + ω * (v l + v (labelRho l))
  else v (labelRho l) + v l

theorem basisVec_of_fixed {l : Label Tag.E6} (h : labelRho l = l) :
    basisVec l = Finsupp.single l 1 := by
  rw [basisVec, ite_eq_left h]

theorem basisVec_of_first {l : Label Tag.E6} (h : labelRho l ≠ l) (hf : IsFirst l) :
    basisVec l = Finsupp.single l 1 + Finsupp.single (labelRho l) 1 := by
  rw [basisVec, ite_eq_right h, ite_eq_left hf]

theorem basisVec_of_second {l : Label Tag.E6} (h : labelRho l ≠ l) (hf : ¬IsFirst l) :
    basisVec l = ω • Finsupp.single (labelRho l) 1 + ω ^ 2 • Finsupp.single l 1 := by
  rw [basisVec, ite_eq_right h, ite_eq_right hf]

theorem coordK_of_fixed {l : Label Tag.E6} (h : labelRho l = l) (v : V) : coordK v l = v l := by
  rw [coordK, ite_eq_left h]

theorem coordK_of_first {l : Label Tag.E6} (h : labelRho l ≠ l) (hf : IsFirst l) (v : V) :
    coordK v l = v l + ω * (v l + v (labelRho l)) := by
  rw [coordK, ite_eq_right h, ite_eq_left hf]

theorem coordK_of_second {l : Label Tag.E6} (h : labelRho l ≠ l) (hf : ¬IsFirst l) (v : V) :
    coordK v l = v (labelRho l) + v l := by
  rw [coordK, ite_eq_right h, ite_eq_right hf]

theorem basisVec_apply_of_ne {l m : Label Tag.E6} (h₁ : m ≠ l) (h₂ : m ≠ labelRho l) :
    basisVec l m = 0 := by
  by_cases hl : labelRho l = l
  · rw [basisVec_of_fixed hl, Finsupp.single_apply, ite_eq_right (Ne.symm h₁)]
  · by_cases hf : IsFirst l
    · rw [basisVec_of_first hl hf, Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_right (Ne.symm h₁), Finsupp.single_apply, ite_eq_right (Ne.symm h₂), add_zero]
    · rw [basisVec_of_second hl hf, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
        Finsupp.single_apply, ite_eq_right (Ne.symm h₂), Finsupp.single_apply,
        ite_eq_right (Ne.symm h₁), smul_zero, smul_zero, add_zero]

theorem labelRho_ne_iff {l : Label Tag.E6} :
    labelRho (labelRho l) ≠ labelRho l ↔ labelRho l ≠ l := by
  rw [labelRho_labelRho]
  exact ne_comm

theorem sum_coordK_smul
    (v : V) : ∑ l, coordK v l • basisVec l = v := by
  ext m
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have hzero : ∀ l ∈ (Finset.univ : Finset (Label Tag.E6)), l ∉ ({m, labelRho m} : Finset _) →
      coordK v l * basisVec l m = 0 := by
    intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rw [basisVec_apply_of_ne (Ne.symm hl.1) (fun e => hl.2 (by rw [e, labelRho_labelRho])),
      mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  by_cases hm : labelRho m = m
  · rw [hm, Finset.pair_eq_singleton, Finset.sum_singleton, basisVec_of_fixed hm,
      coordK_of_fixed hm,
      Finsupp.single_eq_same, mul_one]
  · have hne : m ≠ labelRho m := Ne.symm hm
    rw [Finset.sum_pair hne]
    have hm' : labelRho (labelRho m) ≠ labelRho m := labelRho_ne_iff.2 hm
    by_cases hf : IsFirst m
    · have hf' : ¬IsFirst (labelRho m) := (isFirst_iff_not_isFirst hm).1 hf
      rw [basisVec_of_first hm hf, coordK_of_first hm hf, basisVec_of_second hm' hf',
        coordK_of_second hm' hf', labelRho_labelRho]
      simp [hne]
      linear_combination ω * (v m + v (labelRho m)) * two_eq_zero_K
    · have hf' : IsFirst (labelRho m) :=
        (isFirst_iff_not_isFirst hm').2 (by rwa [labelRho_labelRho])
      rw [basisVec_of_second hm hf, coordK_of_second hm hf, basisVec_of_first hm' hf',
        coordK_of_first hm' hf', labelRho_labelRho]
      simp [hne]
      linear_combination (v (labelRho m) + v m) * C2E6Overlap.omega_sq_add_omega_add_one -
        v m * two_eq_zero_K

theorem span_basisVec :
    Submodule.span K (Set.range basisVec) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  rw [← sum_coordK_smul v]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem linearIndependent_basisVec :
    LinearIndependent K basisVec :=
  linearIndependent_of_top_le_span_of_card_eq_finrank span_basisVec.ge
    (by rw [Module.finrank_finsupp_self])

@[expose] def basisK :
    Module.Basis (Label Tag.E6) K V :=
  Module.Basis.mk linearIndependent_basisVec span_basisVec.ge

theorem basisK_apply
    (l : Label Tag.E6) : basisK l = basisVec l := Module.Basis.mk_apply _ _ _

theorem basisK_repr
    (v : V) (l : Label Tag.E6) : basisK.repr v l = coordK v l := by
  have h := basisK.repr_sum_self (coordK v)
  conv_lhs => rw [← sum_coordK_smul v]
  simp only [← basisK_apply] at h ⊢
  rw [h]

theorem sqV_add (v w : V) : sqV (v + w) = sqV v + sqV w :=
  Finsupp.mapRange_add (map_add barHom) v w

theorem sqV_smul (c : K) (v : V) : sqV (c • v) = c ^ 2 • sqV v := by
  ext l
  rw [sqV_apply, Finsupp.smul_apply, Finsupp.smul_apply, sqV_apply, smul_eq_mul, smul_eq_mul,
    mul_pow]

theorem sqV_sqV (v : V) : sqV (sqV v) = v := by
  ext l
  rw [sqV_apply, sqV_apply]
  exact C2E6Overlap.bar_bar (v l)

theorem fixedMap_add (v w : V) : fixedMap (v + w) = fixedMap v + fixedMap w := by
  rw [fixedMap, sqV_add, map_add]
  rfl

theorem fixedMap_smul (c : K) (v : V) : fixedMap (c • v) = c ^ 2 • fixedMap v := by
  rw [fixedMap, sqV_smul, map_smul]
  rfl

theorem fixedMap_sum (s : Finset (Label Tag.E6)) (g : Label Tag.E6 → V) :
    fixedMap (∑ l ∈ s, g l) = ∑ l ∈ s, fixedMap (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fixedMap, sqV]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fixedMap_add, ih]

theorem fixedMap_single (l : Label Tag.E6) (c : K) :
    fixedMap (Finsupp.single l c) = Finsupp.single (labelRho l) (c ^ 2) := by
  ext m
  rw [fixedMap_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : l = labelRho m
  · rw [ite_eq_left h, ite_eq_left (by rw [h, labelRho_labelRho])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [← h', labelRho_labelRho])),
      zero_pow two_ne_zero]

theorem fixedMap_basisVec (l : Label Tag.E6) : fixedMap (basisVec l) = basisVec l := by
  by_cases hl : labelRho l = l
  · rw [basisVec_of_fixed hl, fixedMap_single, hl, one_pow]
  · by_cases hf : IsFirst l
    · rw [basisVec_of_first hl hf, fixedMap_add, fixedMap_single, fixedMap_single,
        labelRho_labelRho, one_pow, add_comm]
    · rw [basisVec_of_second hl hf, fixedMap_add, fixedMap_smul, fixedMap_smul, fixedMap_single,
        fixedMap_single, labelRho_labelRho, one_pow, ← pow_mul, add_comm]
      have h4 : ω ^ (2 * 2) = ω := by
        rw [show 2 * 2 = 3 + 1 by rfl, pow_succ, omega_cube, one_mul]
      rw [h4]

theorem fixedMap_eq_sum
    (v : V) : fixedMap v = ∑ l, coordK v l ^ 2 • basisVec l := by
  conv_lhs => rw [← sum_coordK_smul v]
  rw [fixedMap_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [fixedMap_smul, fixedMap_basisVec]

theorem coordK_fixedMap
    (v : V) (l : Label Tag.E6) : coordK (fixedMap v) l = coordK v l ^ 2 := by
  rw [← basisK_repr, fixedMap_eq_sum]
  simp only [← basisK_apply]
  rw [basisK.repr_sum_self]

theorem fixedMap_eq_self_iff
    (v : V) : fixedMap v = v ↔ ∀ l, coordK v l ^ 2 = coordK v l := by
  constructor
  · intro h l
    rw [← coordK_fixedMap, h]
  · intro h
    rw [fixedMap_eq_sum]
    conv_rhs => rw [← sum_coordK_smul v]
    exact Finset.sum_congr rfl fun l _ => by rw [h l]

end CFSG.Monster.B.E6.FixedE6
