
module


public import CFSG.Monster.B.Co2.MatrixIso

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

open scoped Pointwise

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem stabOrbitSet_disjoint
    {s t : ℕ} (hs : s < 3) (ht : t < 3) (hst : s ≠ t) :
    Disjoint (stabOrbitSet s) (stabOrbitSet t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  have h1 := ((mem_stabOrbit_iff hs).1 hxs).2
  have h2 := ((mem_stabOrbit_iff ht).1 hxt).2
  exact hst (h1.symm.trans h2)

theorem stabOrbitSet_zero : stabOrbitSet 0 = {0} := by
  ext x
  simp only [stabOrbitSet, Set.mem_ofPred_eq, stabOrbit_zero, List.mem_singleton,
    Set.mem_singleton_iff]
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩

theorem ncard_stabOrbitSet' {t : ℕ} (ht : t < 3) :
    (stabOrbitSet t).ncard = [1, 891, 1408][t]! := by
  rw [ncard_stabOrbitSet ht, stabOrbit_length ht]
  interval_cases t <;> rfl

theorem stabOrbitSet_cover :
    stabOrbitSet 0 ∪ stabOrbitSet 1 ∪ stabOrbitSet 2 = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  obtain ⟨t, ht, hx⟩ := stabOrbit_cover x x.2
  interval_cases t
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem orbit_stab_eq_of_mem
    {t : ℕ} (ht : t < 3) {x : Ω} (hx : x ∈ stabOrbitSet t) :
    MulAction.orbit (MulAction.stabilizer Pgrp (0 : Ω)) x = stabOrbitSet t := by
  rw [← orbit_stabilizer_eq ht] at hx ⊢
  exact MulAction.orbit_eq_iff.2 hx

theorem block_invariant
    {B : Set Ω} (hB : MulAction.IsBlock Pgrp B) (h0 : (0 : Ω) ∈ B)
    (g : MulAction.stabilizer Pgrp (0 : Ω)) {x : Ω} (hx : x ∈ B) : (g : Pgrp) • x ∈ B := by
  have hg0 : (g : Pgrp) • (0 : Ω) = 0 := g.2
  rcases hB.smul_eq_or_disjoint (g : Pgrp) with h | h
  · rw [← h]
    exact Set.smul_mem_smul_set hx
  · exfalso
    have : (0 : Ω) ∈ (g : Pgrp) • B := Set.mem_smul_set.2 ⟨0, h0, hg0⟩
    exact Set.disjoint_left.1 h this h0

theorem stabOrbitSet_subset_of_meet
    {B : Set Ω} (hB : MulAction.IsBlock Pgrp B) (h0 : (0 : Ω) ∈ B)
    {t : ℕ} (ht : t < 3) {x : Ω} (hxB : x ∈ B) (hxt : x ∈ stabOrbitSet t) : stabOrbitSet t ⊆ B := by
  rw [← orbit_stab_eq_of_mem ht hxt]
  rintro _ ⟨g, rfl⟩
  exact block_invariant hB h0 g hxB

theorem block_trivial
    {B : Set Ω} (hB : MulAction.IsBlock Pgrp B) (h0 : (0 : Ω) ∈ B) :
    MulAction.IsTrivialBlock B := by
  classical
  have hsplit : ∀ t, t < 3 → B ∩ stabOrbitSet t = ∅ ∨ stabOrbitSet t ⊆ B := by
    intro t ht
    by_cases h : (B ∩ stabOrbitSet t).Nonempty
    · obtain ⟨x, hxB, hxt⟩ := h
      exact Or.inr (stabOrbitSet_subset_of_meet hB h0 ht hxB hxt)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 h)
  have hB_eq : B = (B ∩ stabOrbitSet 0) ∪ (B ∩ stabOrbitSet 1) ∪ (B ∩ stabOrbitSet 2) := by
    rw [← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left, stabOrbitSet_cover,
      Set.inter_univ]
  have h0' : B ∩ stabOrbitSet 0 = stabOrbitSet 0 := by
    rw [stabOrbitSet_zero, Set.inter_eq_right, Set.singleton_subset_iff]
    exact h0
  have hfin : ∀ S : Set Ω, S.Finite := fun S => Set.toFinite S
  have hdvd := hB.ncard_dvd_card ⟨0, h0⟩
  have hΩ : Nat.card Ω = 2300 := by simp [Ω]
  rw [hΩ] at hdvd
  have hc0 := ncard_stabOrbitSet' (t := 0) (by norm_num)
  have hc1 := ncard_stabOrbitSet' (t := 1) (by norm_num)
  have hc2 := ncard_stabOrbitSet' (t := 2) (by norm_num)
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hc0 hc1 hc2
  have hd01 := stabOrbitSet_disjoint (s := 0) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  have hd02 := stabOrbitSet_disjoint (s := 0) (t := 2) (by norm_num) (by norm_num) (by norm_num)
  have hd12 := stabOrbitSet_disjoint (s := 1) (t := 2) (by norm_num) (by norm_num) (by norm_num)
  rcases hsplit 1 (by norm_num) with h1 | h1 <;> rcases hsplit 2 (by norm_num) with h2 | h2
  ·
    left
    rw [hB_eq, h0', h1, h2, Set.union_empty, Set.union_empty, stabOrbitSet_zero]
    exact Set.subsingleton_singleton
  ·
    exfalso
    rw [hB_eq, h0', h1, Set.union_empty, Set.inter_eq_right.2 h2,
      Set.ncard_union_eq hd02 (hfin _) (hfin _), hc0, hc2] at hdvd
    exact absurd hdvd (by decide)
  ·
    exfalso
    rw [hB_eq, h0', h2, Set.union_empty, Set.inter_eq_right.2 h1,
      Set.ncard_union_eq hd01 (hfin _) (hfin _), hc0, hc1] at hdvd
    exact absurd hdvd (by decide)
  ·
    right
    rw [hB_eq, h0', Set.inter_eq_right.2 h1, Set.inter_eq_right.2 h2, stabOrbitSet_cover]

instance isPreprimitive_Pgrp :
    MulAction.IsPreprimitive Pgrp Ω :=
  MulAction.IsPreprimitive.of_isTrivialBlock_base (0 : Ω) fun h0 hB => block_trivial hB h0

instance finite_Pgrp : Finite Pgrp := inferInstance

@[expose] def pa' : Pgrp := ⟨pa, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def pb' : Pgrp := ⟨pb, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem closure_pa'_pb' : Subgroup.closure ({pa', pb'} : Set Pgrp) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (G := Equiv.Perm Ω) (k := ({pa, pb} : Set _))
  have e : (((↑) : Pgrp → Equiv.Perm Ω) ⁻¹' ({pa, pb} : Set _)) = ({pa', pb'} : Set Pgrp) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [← e]
  exact h

attribute [local instance] aAction

@[expose] def aActionHom :
    Ω →ₑ[fun a : Agrp => (agrpEquivPgrp a : Pgrp)] Ω where
  toFun := id
  map_smul' _ _ := rfl

theorem kOp_apply_mul (a b : OLq) (x : L2) : kOp (a * b) x = kOp b (kOp a x) := by
  rw [kOp_mul, Module.End.mul_apply]

theorem kOp_inv_apply (g : OLq) (x : L2) : kOp g⁻¹ (kOp g x) = x := by
  rw [← kOp_apply_mul, mul_inv_cancel, kOp_one, Module.End.one_apply]

theorem Kstab_kOp (g : OLq) (x : L2) :
    Kstab (kOp g x) = (Kstab x).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext k
  rw [Subgroup.mem_map]
  constructor
  · intro hk
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · change kOp (g * k * g⁻¹) x = x
      have hk' : kOp k (kOp g x) = kOp g x := hk
      rw [kOp_apply_mul, kOp_apply_mul, hk', kOp_inv_apply]
    · simp [mul_assoc]
  · rintro ⟨h, hh, rfl⟩
    change kOp (g⁻¹ * h * g⁻¹⁻¹) (kOp g x) = kOp g x
    have hh' : kOp h x = x := hh
    rw [inv_inv, kOp_apply_mul, kOp_apply_mul, kOp_inv_apply, hh']

@[expose] def kstabEquiv (g : OLq) (x : L2) : Kstab (kOp g x) ≃* Kstab x :=
  (MulEquiv.subgroupCongr (Kstab_kOp g x)).trans
    (Subgroup.equivMapOfInjective (Kstab x) (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm

theorem nonempty_kstabEquiv {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    Nonempty (Kstab (classOf u) ≃* Kstab v0) := by
  obtain ⟨p, hp⟩ := exists_Pvis_of_short (x := v0) (y := classOf u)
    ⟨_, vMinus_zero_one_mem, rfl⟩ ⟨u, hu, rfl⟩
  have e : kOp (QuotientGroup.mk p.1.2) v0 = classOf u := hp
  exact ⟨(MulEquiv.subgroupCongr (congrArg Kstab e)).symm.trans (kstabEquiv _ v0)⟩

theorem natCard_Kv :
    Nat.card (Kstab v0) = 42305421312000 :=
  natCard_Kstab_of_short ⟨_, vMinus_zero_one_mem, rfl⟩

instance finite_Kv :
    Finite (Kstab v0) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Kv]; norm_num)

theorem isSimpleGroup_Pgrp :
    IsSimpleGroup Pgrp := by
  refine CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    (by simp [Ω]) pa' pb' closure_pa'_pb' (0 : Ω) ?_ ?_
  · have h1 : orderOf pa' = 2 := by rw [← Subgroup.orderOf_coe]; exact orderOf_pa
    have h2 : orderOf pb' = 5 := by rw [← Subgroup.orderOf_coe]; exact orderOf_pb
    rw [h1, h2]
    norm_num
  · have h3 : orderOf (pa' * pb') = 23 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_pa_mul_pb
    rw [h3, natCard_stabilizer_Pgrp]
    norm_num

theorem isSimpleGroup_Agrp :
    IsSimpleGroup Agrp :=
  haveI := isSimpleGroup_Pgrp
  agrpEquivPgrp.isSimpleGroup

theorem natCard_Agrp :
    Nat.card Agrp = 42305421312000 :=
  (Nat.card_congr agrpEquivPgrp.toEquiv).trans natCard_Pgrp

theorem nontrivial_Agrp :
    Nontrivial Agrp := isSimpleGroup_Agrp.toNontrivial

attribute [local instance] aAction

theorem isPreprimitive_aAction :
    MulAction.IsPreprimitive Agrp Ω :=
  (MulAction.isPreprimitive_congr (f := aActionHom) agrpEquivPgrp.surjective
    Function.bijective_id).2 isPreprimitive_Pgrp

theorem faithfulSMul_aAction :
    FaithfulSMul Agrp Ω :=
  ⟨fun h => agrpEquivPgrp.injective (Subtype.ext (Equiv.ext fun j => h j))⟩

theorem Agrp_eq_Kv :
    Agrp = Kstab v0 :=
  Subgroup.eq_of_le_of_card_ge Agrp_le (by rw [natCard_Kv, natCard_Agrp])

theorem native_short_stabilizer_simple :
    (∀ u ∈ minVecs, IsSimpleGroup (Kstab (classOf u)) ∧ Nontrivial (Kstab (classOf u)) ∧
      Nat.card (Kstab (classOf u)) = 42305421312000) ∧
    Agrp = Kstab (classOf (Griess.vMinus 0 1)) ∧
    FaithfulSMul Agrp Ω ∧ MulAction.IsPreprimitive Agrp Ω ∧ MulAction.IsPreprimitive Pgrp Ω := by
  have hsimple : IsSimpleGroup (Kstab v0) := by
    have e : Agrp ≃* Kstab v0 := MulEquiv.subgroupCongr Agrp_eq_Kv
    have := isSimpleGroup_Agrp
    exact e.symm.isSimpleGroup
  refine ⟨fun u hu => ?_, Agrp_eq_Kv, faithfulSMul_aAction, isPreprimitive_aAction,
    isPreprimitive_Pgrp⟩
  obtain ⟨e⟩ := nonempty_kstabEquiv hu
  have := hsimple
  have : IsSimpleGroup (Kstab (classOf u)) := e.isSimpleGroup
  exact ⟨inferInstance, IsSimpleGroup.toNontrivial, natCard_Kstab_of_short ⟨u, hu, rfl⟩⟩

end CFSG.Monster.B.Co2
