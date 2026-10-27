module

public import CFSG.Monster.B.TwoA.Fischer.SplitAffine

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (lab) in
@[expose] def labelLayer (C : Set V) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (i : ℕ) : Set S :=
  {r | ∃ f : C →₀ ZMod 2, ((cliqueLabelMap lab C f).toMul : S) = r ∧ f.support.card = i ∧
    ∀ g : C →₀ ZMod 2, ((cliqueLabelMap lab C g).toMul : S) = r → i ≤ g.support.card}

section Layers

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

variable (lab) in
@[expose] def labProd (T : Finset C) : S :=
  ((∏ z ∈ T, cliqueGen (lab := lab) z : Subgroup.closure (lab '' C)) : S)

theorem labProd_mem (T : Finset C) : labProd lab T ∈ Subgroup.closure (lab '' C) :=
  (∏ z ∈ T, cliqueGen (lab := lab) z).2

theorem coe_toMul_cliqueLabelMap (f : C →₀ ZMod 2) :
    ((cliqueLabelMap lab C f).toMul : S) = labProd lab f.support := by
  rw [cliqueLabelMap_apply, toMul_sum]
  rfl

theorem eq_indicWord (f : C →₀ ZMod 2) : f = indicWord f.support := by
  classical
  ext z
  rw [indicWord, Finsupp.onFinset_apply]
  by_cases h : z ∈ f.support
  · rw [ite_eq_left h]
    exact zmod_two_eq_one _ (Finsupp.mem_support_iff.1 h)
  · rw [ite_eq_right h]
    exact Finsupp.notMem_support_iff.1 h

theorem labProd_eq (T : Finset C) :
    labProd lab T = ((cliqueLabelMap lab C (indicWord T)).toMul : S) := by
  rw [coe_toMul_cliqueLabelMap, support_indicWord]

theorem mem_labelLayer_iff (r : S) (i : ℕ) :
    r ∈ labelLayer lab C i ↔ ∃ T : Finset C, labProd lab T = r ∧ T.card = i ∧
      ∀ T' : Finset C, labProd lab T' = r → i ≤ T'.card := by
  constructor
  · rintro ⟨f, hf, hfi, hmin⟩
    refine ⟨f.support, by rw [← coe_toMul_cliqueLabelMap]; exact hf, hfi, fun T' hT' => ?_⟩
    have := hmin (indicWord T') (by rw [← labProd_eq]; exact hT')
    rwa [support_indicWord] at this
  · rintro ⟨T, hT, hTi, hmin⟩
    refine ⟨indicWord T, by rw [← labProd_eq]; exact hT, by rw [support_indicWord]; exact hTi,
      fun g hg => hmin g.support (by rw [← coe_toMul_cliqueLabelMap]; exact hg)⟩

theorem card_le_of_mem_labelLayer {r : S} {i : ℕ} (hr : r ∈ labelLayer lab C i)
    {T : Finset C} (hT : labProd lab T = r) : i ≤ T.card := by
  obtain ⟨-, -, -, hmin⟩ := (mem_labelLayer_iff r i).1 hr
  exact hmin T hT

theorem eq_of_mem_labelLayer {r : S} {i j : ℕ} (hi : r ∈ labelLayer lab C i)
    (hj : r ∈ labelLayer lab C j) : i = j := by
  obtain ⟨T, hT, hTi, -⟩ := (mem_labelLayer_iff r i).1 hi
  obtain ⟨T', hT', hT'j, -⟩ := (mem_labelLayer_iff r j).1 hj
  have h1 := card_le_of_mem_labelLayer hi hT'
  have h2 := card_le_of_mem_labelLayer hj hT
  omega

theorem disjoint_labelLayer {i j : ℕ} (h : i ≠ j) :
    Disjoint (labelLayer lab C i) (labelLayer lab C j) :=
  Set.disjoint_left.2 fun _ hi hj => h (eq_of_mem_labelLayer hi hj)

theorem labProd_empty : labProd lab (∅ : Finset C) = 1 := by
  rw [labProd, Finset.prod_empty]
  rfl

theorem labProd_singleton (z : C) : labProd lab {z} = lab z := by
  rw [labProd, Finset.prod_singleton]
  rfl

theorem labProd_pair [DecidableEq C] {z z' : C} (h : z ≠ z') :
    labProd lab {z, z'} = lab z * lab z' := by
  rw [labProd, Finset.prod_insert (by simpa using h), Finset.prod_singleton]
  rfl

theorem labelLayer_zero : labelLayer lab C 0 = {1} := by
  ext r
  rw [mem_labelLayer_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨T, hT, hT0, -⟩
    rw [Finset.card_eq_zero.1 hT0, labProd_empty] at hT
    exact hT.symm
  · rintro rfl
    exact ⟨∅, labProd_empty, rfl, fun _ _ => Nat.zero_le _⟩

end Layers

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

section Max

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hC

theorem eq_of_labProd_eq {T T' : Finset C} (h5 : T.card + T'.card ≤ 5)
    (h : labProd lab T = labProd lab T') : T = T' := by
  classical
  obtain ⟨_, -, -, -, hmin, -⟩ := hS.clique_code_steiner_design hC
  have hfg : cliqueLabelMap lab C (indicWord T) = cliqueLabelMap lab C (indicWord T') := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [← labProd_eq, ← labProd_eq]
    exact h
  have hK : indicWord T + indicWord T' ∈ cliqueCode lab C := by
    rw [cliqueCode, LinearMap.mem_ker, map_add, hfg, additive_add_self]
  have h0 : indicWord T + indicWord T' = 0 := by
    by_contra hne
    have h6 := hmin _ hK hne
    have h1 := Finset.card_le_card (Finsupp.support_add (g₁ := indicWord T) (g₂ := indicWord T'))
    have h2 := Finset.card_union_le (indicWord T).support (indicWord T').support
    rw [support_indicWord, support_indicWord] at h1 h2
    omega
  have hfg' : indicWord T = indicWord T' := by
    ext z
    have := congrArg (fun φ : C →₀ ZMod 2 => φ z) h0
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    revert this
    generalize indicWord T z = a
    generalize indicWord T' z = b
    revert a b
    decide
  rw [← support_indicWord T, ← support_indicWord T']
  exact congrArg Finsupp.support hfg'

omit [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem lab_ne_one {z : V} (hz : z ∈ C) : lab z ≠ 1 := by
  intro h
  have h2 := hS.orderOf_lab z (hC.1.1 hz)
  rw [h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem labelLayer_one : labelLayer lab C 1 = lab '' C := by
  ext r
  rw [mem_labelLayer_iff]
  constructor
  · rintro ⟨T, hT, hT1, -⟩
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.1 hT1
    rw [labProd_singleton] at hT
    exact ⟨z, z.2, hT⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨{⟨a, ha⟩}, labProd_singleton _, Finset.card_singleton _, fun T' hT' => ?_⟩
    by_contra h0
    have hT0 : T' = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [hT0, labProd_empty] at hT'
    exact hS.lab_ne_one hC ha hT'.symm

theorem labelLayer_two :
    labelLayer lab C 2 = {r | ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧ r = lab a * lab b} := by
  classical
  ext r
  rw [mem_labelLayer_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨T, hT, hT2, -⟩
    obtain ⟨z, z', hzz, rfl⟩ := Finset.card_eq_two.1 hT2
    rw [labProd_pair hzz] at hT
    exact ⟨z, z.2, z', z'.2, fun h => hzz (Subtype.ext h), hT.symm⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    have hne : (⟨a, ha⟩ : C) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    refine ⟨{⟨a, ha⟩, ⟨b, hb⟩}, labProd_pair hne, Finset.card_pair hne, fun T' hT' => ?_⟩
    by_contra hlt
    have h := hS.eq_of_labProd_eq hC (T := {⟨a, ha⟩, ⟨b, hb⟩}) (T' := T')
      (by rw [Finset.card_pair hne]; omega) (by rw [labProd_pair hne, hT'])
    rw [← h, Finset.card_pair hne] at hlt
    omega

theorem labelLayer_subset (i : ℕ) : labelLayer lab C i ⊆ ptStab act lab Y C := by
  intro r hr
  obtain ⟨T, rfl, -, -⟩ := (mem_labelLayer_iff r i).1 hr
  rw [hS.ptStab_eq_closure_of_isSliceMaxClique hC]
  exact labProd_mem T

theorem exists_mem_labelLayer {r : S} (hr : r ∈ ptStab act lab Y C) :
    ∃ i ≤ 3, r ∈ labelLayer lab C i := by
  classical
  rw [hS.ptStab_eq_closure_of_isSliceMaxClique hC] at hr
  obtain ⟨T₀, hT₀3, hT₀⟩ := hS.exists_short_prod hC ⟨r, hr⟩
  have hP : ∃ n, ∃ T : Finset C, labProd lab T = r ∧ T.card = n :=
    ⟨T₀.card, T₀, congrArg Subtype.val hT₀, rfl⟩
  obtain ⟨T, hT, hTn⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, (Nat.find_min' hP ⟨T₀, congrArg Subtype.val hT₀, rfl⟩).trans hT₀3,
    (mem_labelLayer_iff r _).2 ⟨T, hT, hTn, fun T' hT' => Nat.find_min' hP ⟨T', hT', rfl⟩⟩⟩

theorem ptStab_eq_union_labelLayer :
    (ptStab act lab Y C : Set S) = labelLayer lab C 0 ∪ labelLayer lab C 1 ∪
      labelLayer lab C 2 ∪ labelLayer lab C 3 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨i, hi, hri⟩ := hS.exists_mem_labelLayer hC hr
    interval_cases i
    · exact Or.inl (Or.inl (Or.inl hri))
    · exact Or.inl (Or.inl (Or.inr hri))
    · exact Or.inl (Or.inr hri)
    · exact Or.inr hri
  · rintro r (((h | h) | h) | h) <;> exact hS.labelLayer_subset hC _ h

theorem ncard_labelLayer_one : (labelLayer lab C 1).ncard = 22 := by
  rw [hS.labelLayer_one hC, Set.InjOn.ncard_image (hS.injOn.mono hC.1.1),
    hS.ncard_eq_of_isSliceMaxClique hC]

theorem ncard_labelLayer_two : (labelLayer lab C 2).ncard = 231 := by
  classical
  have : Finite C := (hS.finite.subset hC.1.1).to_subtype
  let _ : Fintype C := Fintype.ofFinite C
  have e : labelLayer lab C 2 =
      labProd lab '' ((Finset.univ.powersetCard 2 : Finset (Finset C)) : Set (Finset C)) := by
    ext r
    rw [mem_labelLayer_iff]
    constructor
    · rintro ⟨T, hT, hT2, -⟩
      exact ⟨T, by simpa using hT2, hT⟩
    · rintro ⟨T, hT, rfl⟩
      have hT2 : T.card = 2 := by simpa using hT
      refine ⟨T, rfl, hT2, fun T' hT' => ?_⟩
      by_contra hlt
      have h := hS.eq_of_labProd_eq hC (T := T) (T' := T') (by omega) hT'.symm
      rw [← h] at hlt
      omega
  have hinj : Set.InjOn (labProd lab)
      ((Finset.univ.powersetCard 2 : Finset (Finset C)) : Set (Finset C)) := by
    intro T hT T' hT' h
    have hT2 : T.card = 2 := by simpa using hT
    have hT'2 : T'.card = 2 := by simpa using hT'
    exact hS.eq_of_labProd_eq hC (by omega) h
  rw [e, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hS.ncard_eq_of_isSliceMaxClique hC]
  rfl

omit [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem finite_ptStab : (ptStab act lab Y C : Set S).Finite := by
  have hR : Nat.card (ptStab act lab Y C) = 2 ^ 10 :=
    (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.2.2.2.1
  have : Finite (ptStab act lab Y C) := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  exact Set.toFinite _

omit [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem ncard_ptStab : (ptStab act lab Y C : Set S).ncard = 1024 := by
  have hR : Nat.card (ptStab act lab Y C) = 2 ^ 10 :=
    (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.2.2.2.1
  rw [← Nat.card_coe_set_eq]
  exact hR

theorem ncard_labelLayer_three : (labelLayer lab C 3).ncard = 770 := by
  have hfin : ∀ i, (labelLayer lab C i).Finite := fun i =>
    (hS.finite_ptStab hC).subset (hS.labelLayer_subset hC i)
  have hd : ∀ i j, i ≠ j → Disjoint (labelLayer lab C i) (labelLayer lab C j) :=
    fun i j h => disjoint_labelLayer h
  have hcard := hS.ncard_ptStab hC
  rw [hS.ptStab_eq_union_labelLayer hC,
    Set.ncard_union_eq (Disjoint.union_left (Disjoint.union_left (hd 0 3 (by decide))
      (hd 1 3 (by decide))) (hd 2 3 (by decide))) (((hfin 0).union (hfin 1)).union (hfin 2))
      (hfin 3),
    Set.ncard_union_eq (Disjoint.union_left (hd 0 2 (by decide)) (hd 1 2 (by decide)))
      ((hfin 0).union (hfin 1)) (hfin 2),
    Set.ncard_union_eq (hd 0 1 (by decide)) (hfin 0) (hfin 1), labelLayer_zero,
    Set.ncard_singleton, hS.ncard_labelLayer_one hC, hS.ncard_labelLayer_two hC] at hcard
  omega

end Max

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
