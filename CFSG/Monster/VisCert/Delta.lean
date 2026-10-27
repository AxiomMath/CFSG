module

public import CFSG.Monster.VisCert.FrameData
public import CFSG.Monster.FrameFiber

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible

instance moduleFinite_L2 : Module.Finite (ZMod 2) L2 :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_L2]; norm_num)

instance finite_L2 : Finite L2 := Module.finite_of_finite (ZMod 2)

theorem natCard_C : Nat.card C = 4096 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_C]
  norm_num

theorem natCard_cocode : Nat.card Cocode = 4096 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_cocode]
  norm_num

theorem add_self_cocode (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem exists_pair_eq_one {a : C} (ha : a ≠ 0) : ∃ δ, pair a δ = 1 := by
  obtain ⟨δ, hδ⟩ : ∃ δ, pair a δ ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (eq_zero_of_forall_pair_left h)
  have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact ⟨δ, this _ hδ⟩

@[expose] def shiftδ (a : C) : Cocode :=
  open Classical in if h : a = 0 then 0 else (exists_pair_eq_one h).choose

theorem pair_shiftδ {a : C} (ha : a ≠ 0) : pair a (shiftδ a) = 1 := by
  rw [shiftδ, dite_eq_right ha]
  exact (exists_pair_eq_one ha).choose_spec

@[expose] def pairSet (t : ZMod 2) : Set (C × Cocode) := {p | p.1 ≠ 0 ∧ pair p.1 p.2 = t}

@[expose] def shiftMap (p : C × Cocode) : C × Cocode := (p.1, p.2 + shiftδ p.1)

theorem shiftMap_shiftMap (p : C × Cocode) : shiftMap (shiftMap p) = p := by
  simp only [shiftMap, add_assoc, add_self_cocode, add_zero]

theorem shiftMap_injective : Function.Injective shiftMap := fun p q h => by
  rw [← shiftMap_shiftMap p, h, shiftMap_shiftMap]

theorem shiftMap_mem_pairSet {t : ZMod 2} {p : C × Cocode} (hp : p ∈ pairSet t) :
    shiftMap p ∈ pairSet (t + 1) :=
  ⟨hp.1, by rw [shiftMap, map_add, hp.2, pair_shiftδ hp.1]⟩

theorem image_shiftMap_pairSet : shiftMap '' pairSet 0 = pairSet 1 := by
  refine Set.Subset.antisymm ?_ fun p hp => ?_
  · rintro _ ⟨p, hp, rfl⟩
    simpa using shiftMap_mem_pairSet hp
  · refine ⟨shiftMap p, ?_, shiftMap_shiftMap p⟩
    have h := shiftMap_mem_pairSet hp
    rwa [show (1 + 1 : ZMod 2) = 0 from rfl] at h

theorem ncard_pairSet_one : (pairSet 1).ncard = (pairSet 0).ncard := by
  rw [← image_shiftMap_pairSet, Set.ncard_image_of_injective _ shiftMap_injective]

theorem pairSet_union : pairSet 0 ∪ pairSet 1 = ({0}ᶜ : Set C) ×ˢ (Set.univ : Set Cocode) := by
  ext p
  simp only [pairSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_compl_iff,
    Set.mem_singleton_iff, Set.mem_univ, and_true]
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases this (pair p.1 p.2) with h | h <;> simp [h]

theorem disjoint_pairSet : Disjoint (pairSet 0) (pairSet 1) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, h0⟩ ⟨-, h1⟩
  exact absurd (h0.symm.trans h1) (by decide)

theorem ncard_pairSet_zero : (pairSet 0).ncard = 4095 * 2048 := by
  have h := Set.ncard_union_eq disjoint_pairSet
  rw [pairSet_union, ncard_pairSet_one, Set.ncard_prod, Set.ncard_compl, Set.ncard_singleton,
    Set.ncard_univ, natCard_C, natCard_cocode] at h
  omega

theorem singularPairs_eq :
    {p : C × Cocode | pair p.1 p.2 = 0} = ({0} : Set C) ×ˢ (Set.univ : Set Cocode) ∪ pairSet 0 := by
  ext p
  simp only [pairSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_univ, and_true]
  by_cases h : p.1 = 0
  · simp [h]
  · simp [h]

theorem ncard_singularPairs : {p : C × Cocode | pair p.1 p.2 = 0}.ncard = 8390656 := by
  rw [singularPairs_eq, Set.ncard_union_eq, Set.ncard_prod, Set.ncard_singleton, Set.ncard_univ,
    natCard_cocode, ncard_pairSet_zero]
  rw [Set.disjoint_left]
  rintro p ⟨h0, -⟩ ⟨h1, -⟩
  exact h1 h0

theorem singular_eq_image :
    {v : L2 | qL v = 0} = phi0Equiv '' {p : C × Cocode | pair p.1 p.2 = 0} := by
  ext v
  constructor
  · intro hv
    refine ⟨phi0Equiv.symm v, ?_, phi0Equiv.apply_symm_apply v⟩
    have h := qL_phi0 (phi0Equiv.symm v).1 (phi0Equiv.symm v).2
    have e : phi0 ((phi0Equiv.symm v).1, (phi0Equiv.symm v).2) = v :=
      phi0Equiv.apply_symm_apply v
    rw [e] at h
    exact h.symm.trans hv
  · rintro ⟨p, hp, rfl⟩
    exact (qL_phi0 p.1 p.2).trans hp

theorem ncard_singular : {v : L2 | qL v = 0}.ncard = 8390656 := by
  rw [singular_eq_image, Set.ncard_image_of_injective _ phi0Equiv.injective, ncard_singularPairs]

@[expose] def shortSet : Set L2 := {c | ∃ u ∈ minVecs, classOf u = c}

theorem ncard_shortSet : shortSet.ncard = 98280 := card_classes

theorem shortSet_subset_singular : shortSet ⊆ {v : L2 | qL v = 0} := by
  rintro _ ⟨u, hu, rfl⟩
  exact Griess.qL_classOf_minVecs hu

theorem zero_notMem_shortSet : (0 : L2) ∉ shortSet := by
  rintro ⟨u, hu, h0⟩
  rw [classOf_of_mem hu.1, Submodule.Quotient.mk_eq_zero, mem_two_range_iff] at h0
  obtain ⟨w, hw'⟩ := h0
  have hw : (2 : ℤ) • (w : Fin 24 → ℤ) = u := hw'
  have hn : normSq u = 32 := (mem_minVecs_iff.1 hu).2
  have hw0 : (w : Fin 24 → ℤ) ≠ 0 := by
    intro h
    apply minVecs_ne_zero hu
    rw [← hw, h, smul_zero]
  have h32 := normSq_ge w.2 hw0
  have : normSq u = 4 * normSq (w : Fin 24 → ℤ) := by
    rw [← normSq_two_smul, hw]
  omega

theorem frameDelta_eq_sdiff : frameDelta = {v : L2 | qL v = 0} \ insert 0 shortSet := by
  ext v
  simp only [frameDelta, shortSet, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, not_or]
  tauto

theorem ncard_frameDelta : frameDelta.ncard = 8292375 := by
  rw [frameDelta_eq_sdiff,
    Set.ncard_sdiff (Set.insert_subset_iff.2 ⟨by simp, shortSet_subset_singular⟩), ncard_singular,
    Set.ncard_insert_of_notMem zero_notMem_shortSet, ncard_shortSet]

theorem hInt_latHom (g : latticeO) (u : codeLatticeSubgroup allOnes_mem_C) :
    hInt (latHom g u : Fin 24 → ℤ) (latHom g u) = hInt (u : Fin 24 → ℤ) u := by
  apply Int.cast_injective (α := ℚ)
  rw [hInt_eq_codeForm allOnes_mem_C weight_mod_four' (latHom g u).2 (latHom g u).2,
    hInt_eq_codeForm allOnes_mem_C weight_mod_four' u.2 u.2]
  change codeForm (ratVec (latHom g u)) (ratVec (latHom g u)) = codeForm (ratVec u) (ratVec u)
  rw [ratVec_latHom, codeForm_vecMul_vecMul (mat_mul_transpose g)]

theorem qL_modTwoEnd (g : latticeO) (x : L2) : qL (modTwoEnd g x) = qL x := by
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    rw [modTwoEnd_mk]
    change codeQuadForm C allOnes_mem_C weight_mod_four' (Submodule.Quotient.mk (latHom g u)) =
      codeQuadForm C allOnes_mem_C weight_mod_four' (Submodule.Quotient.mk u)
    rw [codeQuadForm_mk, codeQuadForm_mk, hInt_latHom]

theorem modTwoEnd_inv_apply (g : latticeO) (x : L2) : modTwoEnd g⁻¹ (modTwoEnd g x) = x := by
  rw [← Module.End.mul_apply, ← modTwoEnd_mul, mul_inv_cancel, modTwoEnd_one,
    Module.End.one_apply]

theorem modTwoEnd_classOf (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd g (classOf u) = classOf (latVec (mat g) u) := by
  rw [classOf_of_mem hu, classOf_of_mem (latVec_spec g hu).1, modTwoEnd_mk]
  rfl

theorem modTwoEnd_mem_shortSet (g : latticeO) {x : L2} (hx : x ∈ shortSet) :
    modTwoEnd g x ∈ shortSet := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨_, latVec_mem_minVecs g hu, (modTwoEnd_classOf g hu.1).symm⟩

theorem mem_frameDelta_of (g : latticeO) {x : L2} (hx : x ∈ frameDelta) :
    modTwoEnd g x ∈ frameDelta := by
  obtain ⟨h0, hq, hs⟩ := hx
  refine ⟨fun h => h0 ?_, (qL_modTwoEnd g x).trans hq, fun h => hs ?_⟩
  · rw [← modTwoEnd_inv_apply g x, h, map_zero]
  · rw [← modTwoEnd_inv_apply g x]
    exact modTwoEnd_mem_shortSet g⁻¹ h

theorem modTwoEnd_mem_frameDelta_iff (g : latticeO) {x : L2} :
    modTwoEnd g x ∈ frameDelta ↔ x ∈ frameDelta := by
  refine ⟨fun h => ?_, mem_frameDelta_of g⟩
  rw [← modTwoEnd_inv_apply g x]
  exact mem_frameDelta_of g⁻¹ h

theorem modTwoUnit_smul (g : latticeO) (x : L2) : modTwoUnit g • x = modTwoEnd g x := rfl

theorem smul_mem_frameDelta_iff {u : GLV} (hu : u ∈ Hvis) {x : L2} :
    u • x ∈ frameDelta ↔ x ∈ frameDelta := by
  obtain ⟨g, -, rfl⟩ := mem_Hvis.1 hu
  exact modTwoEnd_mem_frameDelta_iff g

theorem twoΩCls_mem_frameDelta : twoΩCls ∈ frameDelta := by
  refine ⟨frameClass_ne_zero, codeQuadForm_frameClass, ?_⟩
  rintro ⟨u, hu, h⟩
  rw [classOf_of_mem hu.1] at h
  exact (coordinate_frame_mod_two_fiber.2.2.1 ⟨u, hu.1⟩ h) hu.2

end CFSG.Monster.VisCert
