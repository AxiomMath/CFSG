module

public import CFSG.Monster.B.E6.FixedE6RootVector
public import CFSG.Monster.B.E6.StdF4FiberProd

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft
  mem_betaGroup_iff)
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint Matrix
open CFSG.Monster.B.E6.FixedE6 (V fixedL formL gEnd)
open CFSG.Monster.B.E6.FixedE6Root (rootVecOf a0 a0L coe_a0L gL coe_gL_apply gL_mul_apply
  rootVecOf_conj rootVecOf_conj_pair formL_gL formL_a0L_repPoint orderOf_conj_pair
  bijOn_rootVecOf conj_mem_rootClass repPoint_mem_rootClass coe_rootVecOf_repPoint
  gEnd_a0_eq_iff)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem formL_rootVecOf_eq_one_iff
    {p q : stdGroup} (hp : p ∈ rootClass) (hq : q ∈ rootClass) :
    formL (rootVecOf p) (rootVecOf q) = 1 ↔ orderOf (p * q) = 3 := by
  obtain ⟨k, i, rfl, rfl⟩ := FixedE6Root.exists_conj_pair hp hq
  obtain ⟨e₁, e₂⟩ := rootVecOf_conj_pair k i
  rw [e₁, e₂, formL_gL, formL_a0L_repPoint, orderOf_conj_pair]
  fin_cases i <;> decide

@[expose] def x2M :
    ModGL Tag.E6 K := pinnedX Tag.E6 K e2 1

theorem permLattice_e2 :
    permLattice TwistTag.E6.perm (e2 : Fin TwistTag.E6.tag.rank → ℤ) = e2 := by
  have h : permLattice TwistTag.E6.perm (Pi.single (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) =
      Pi.single (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) (1 : ℤ) := by
    decide
  exact h

theorem x2M_mem_stdGroup :
    x2M ∈ stdGroup := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ⟨?_, ?_⟩
  · exact Subgroup.mem_iSup_of_mem e2 (Subgroup.mem_iSup_of_mem
      ⟨isRoot_e2, by decide⟩ (Subgroup.subset_closure ⟨1, rfl⟩))
  · refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
      ⟨pinnedX_mem_adjointGroup _ _, ?_⟩
    have hb : betaGL x2M = x2M :=
      Units.ext (by rw [betaGL_apply, x2M, entrywise_pinnedX, map_one])
    have ht : twistHom TwistTag.E6 K (RingHom.id K) x2M = x2M := by
      have h := twistHom_id_pinnedX (t := TwistTag.E6) two_eq_zero_K isRoot_e2 (1 : K)
      rw [permLattice_e2] at h
      exact h
    rw [twistHom_eq_conj, hb, ← C2E6Std.twistHom_id_eq, ht]

theorem x2M_mem_stdRadical :
    x2M ∈ stdRadical firstJ := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iSup_of_mem e2 (Subgroup.mem_iSup_of_mem
    ⟨⟨isRoot_e2, by decide⟩, fun h => ?_⟩ (Subgroup.subset_closure ⟨1, rfl⟩)),
    graphFixedRootGroup_le _ _ _ x2M_mem_stdGroup⟩
  have h0 := h.1.2 (i6 1) (by rw [nativeUnion_firstJ]; exact fun h => ne_one_of_mem_setA h rfl)
  exact absurd h0 (by decide)

@[expose] def x2 :
    stdGroup := ⟨x2M, x2M_mem_stdGroup⟩

theorem e2_add_repRootL_one : e2 + repRootL 1 = theta := by decide

theorem repRootL_one_ne_neg_e2 : repRootL 1 ≠ -e2 := by decide

theorem gEnd_x2_rootVec :
    gEnd x2 (rootVec Tag.E6 K (repRootL 1)) = rootVec Tag.E6 K (repRootL 1) + a0 := by
  change ((x2M : ModGL Tag.E6 K) : Module.End K V) _ = _
  rw [x2M, pinnedX_eq isRoot_e2, one_smul, one_pow, one_smul, LinearMap.add_apply,
    LinearMap.add_apply, Module.End.one_apply, ad_apply, formTensor_apply,
    bracket_rootVec_rootVec isRoot_e2 (isRoot_repRootL 1) repRootL_one_ne_neg_e2,
    form_rootVec_rootVec repRootL_one_ne_neg_e2, zero_smul, add_zero, e2_add_repRootL_one]
  rfl

theorem rootVecOf_repPoint_one_eq :
    (rootVecOf (repPoint 1) : V) = rootVec Tag.E6 K (repRootL 1) :=
  coe_rootVecOf_repPoint 1

theorem gL_x2_rootVecOf :
    gL x2 (rootVecOf (repPoint 1)) = rootVecOf (repPoint 1) + a0L := by
  apply Subtype.ext
  rw [coe_gL_apply, rootVecOf_repPoint_one_eq, gEnd_x2_rootVec, Submodule.coe_add,
    rootVecOf_repPoint_one_eq, coe_a0L]

theorem fibT_one :
    fibT 1 = repPoint 1 := rfl

theorem fibT_mem_rootClass
    (d : Fin 5) : fibT d ∈ rootClass :=
  (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem gL_a0L_of_mem
    {g : stdGroup} (hg : (g : ModGL Tag.E6 K) ∈ nativeParabolic firstJ) :
    gL g a0L = a0L :=
  Subtype.ext ((gEnd_a0_eq_iff g).2 hg)

theorem a0L_ne_zero : a0L ≠ 0 := by
  intro h
  have h1 := congrArg (fun u : fixedL => (u : V)) h
  simp only [coe_a0L, Submodule.coe_zero] at h1
  rw [FixedE6Root.a0_eq_single] at h1
  exact Finsupp.single_ne_zero.2 one_ne_zero h1

theorem inl_conj
    (g x : stdGroup) :
    (SemidirectProduct.inl (g * x * g⁻¹) : GStar) =
      SemidirectProduct.inl g * SemidirectProduct.inl x * (SemidirectProduct.inl g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem exists_of_mem_fibOrbit
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    ∃ g : stdGroup, (g : ModGL Tag.E6 K) ∈ nativeParabolic firstJ ∧
      x = SemidirectProduct.inl (g * fibT d * g⁻¹) := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  exact ⟨γ.left, hγ, conj_inl_fibT γ d⟩

theorem conjOrbit_fibOrbit_one
    {g : stdGroup} (hg : (g : ModGL Tag.E6 K) ∈ nativeParabolic firstJ) :
    conjOrbit radStar (SemidirectProduct.inl (g * repPoint 1 * g⁻¹)) =
      {SemidirectProduct.inl (g * repPoint 1 * g⁻¹),
        SemidirectProduct.inl (g * x2 * repPoint 1 * (g * x2)⁻¹)} ∧
    rootVecOf (g * x2 * repPoint 1 * (g * x2)⁻¹) = rootVecOf (g * repPoint 1 * g⁻¹) + a0L := by
  have hr1 : rootVecOf (g * repPoint 1 * g⁻¹) = gL g (rootVecOf (repPoint 1)) :=
    rootVecOf_conj (repPoint_mem_rootClass 1) g
  have hr2 : rootVecOf (g * x2 * repPoint 1 * (g * x2)⁻¹) =
      rootVecOf (g * repPoint 1 * g⁻¹) + a0L := by
    rw [rootVecOf_conj (repPoint_mem_rootClass 1), gL_mul_apply, gL_x2_rootVecOf, map_add,
      gL_a0L_of_mem hg, hr1]
  refine ⟨?_, hr2⟩
  have hx : SemidirectProduct.inl (g * repPoint 1 * g⁻¹) ∈ fibOrbit 1 :=
    ⟨SemidirectProduct.inl g, hg, (inl_conj g _).symm⟩
  have hu : (g * x2 * g⁻¹ : stdGroup) ∈ (stdRadical firstJ).subgroupOf stdGroup := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_stdRadical hg x2M_mem_stdRadical
  have hmem : SemidirectProduct.inl (g * x2 * repPoint 1 * (g * x2)⁻¹) ∈
      conjOrbit radStar (SemidirectProduct.inl (g * repPoint 1 * g⁻¹)) := by
    refine ⟨SemidirectProduct.inl (g * x2 * g⁻¹), ⟨_, hu, rfl⟩, ?_⟩
    rw [← inl_conj]
    congr 1
    group
  have hne : SemidirectProduct.inl (g * repPoint 1 * g⁻¹) ≠
      (SemidirectProduct.inl (g * x2 * repPoint 1 * (g * x2)⁻¹) : GStar) := by
    intro h
    have h' := congrArg rootVecOf (SemidirectProduct.inl_injective h)
    rw [hr2] at h'
    exact a0L_ne_zero (by simpa using h'.symm)
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
  · exact Set.insert_subset (mem_conjOrbit_self _ _) (Set.singleton_subset_iff.2 hmem)
  · rw [ncard_conjOrbit_radStar hx, Set.ncard_pair hne]
    decide

theorem image_rootVec_conjOrbit
    {x : GStar} (hx : x ∈ fibOrbit 1) :
    (fun y : GStar => rootVecOf y.left) '' conjOrbit radStar x =
      {rootVecOf x.left, rootVecOf x.left + a0L} := by
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_fibOrbit hx
  rw [fibT_one]
  obtain ⟨h1, h2⟩ := conjOrbit_fibOrbit_one hg
  rw [h1, Set.image_pair]
  simp only [SemidirectProduct.left_inl]
  rw [h2]

theorem form_fibYE_two_one : 0 ≤ fibYE 2 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ repRootL 1) := by
  decide

theorem form_fibYE_two_theta : 0 ≤ fibYE 2 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ theta) := by
  decide

theorem commute_fibT_two_one :
    Commute (fibT 2) (repPoint 1) := by
  refine Subtype.ext ?_
  change (fibT 2 : ModGL Tag.E6 K) * (repPoint 1 : ModGL Tag.E6 K) =
    (repPoint 1 : ModGL Tag.E6 K) * (fibT 2 : ModGL Tag.E6 K)
  rw [coe_fibT, coe_repPoint]
  exact (pinnedX_commute_of_rootForm_nonneg (Or.inr (Or.inl rfl)) (isRoot_fibYE 2)
    (isRoot_repRootL 1) (by decide) form_fibYE_two_one 1 1).eq

theorem fibT_two_mem :
    ((fibT 2 : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic firstJ := by
  rw [← mem_centralizer_rootInv_iff, mul_inv_eq_iff_eq_mul]
  refine Subtype.ext ?_
  change (fibT 2 : ModGL Tag.E6 K) * rootInvM = rootInvM * (fibT 2 : ModGL Tag.E6 K)
  rw [coe_fibT, rootInvM]
  exact (pinnedX_commute_of_rootForm_nonneg (Or.inr (Or.inl rfl)) (isRoot_fibYE 2)
    isRoot_theta (by decide) form_fibYE_two_theta 1 1).eq

theorem conj_fixed_of_rootVecOf
    {q x : stdGroup} (hx : x ∈ rootClass)
    (h : gL q (rootVecOf x) = rootVecOf x) : q * x * q⁻¹ = x :=
  bijOn_rootVecOf.injOn (conj_mem_rootClass hx q) hx (by rw [rootVecOf_conj hx, h])

theorem commute_of_mem_conjOrbit_fibT_one
    {y : GStar}
    (hy : y ∈ conjOrbit radStar (SemidirectProduct.inl (fibT 1))) :
    Commute y (SemidirectProduct.inl (fibT 2)) := by
  have h1 := (conjOrbit_fibOrbit_one (g := 1) (one_mem _)).1
  have e := (conjOrbit_fibOrbit_one (g := 1) (one_mem _)).2
  simp only [one_mul, mul_one, inv_one] at h1 e
  rw [fibT_one, h1] at hy
  have hq : gL (fibT 2) (rootVecOf (repPoint 1)) = rootVecOf (repPoint 1) := by
    rw [← rootVecOf_conj (repPoint_mem_rootClass 1), commute_fibT_two_one.eq,
      mul_inv_cancel_right]
  rcases hy with rfl | rfl
  · exact (commute_fibT_two_one.map SemidirectProduct.inl).symm
  · have hfix : (fibT 2) * (x2 * repPoint 1 * x2⁻¹) * (fibT 2)⁻¹ = x2 * repPoint 1 * x2⁻¹ := by
      refine conj_fixed_of_rootVecOf (conj_mem_rootClass (repPoint_mem_rootClass 1) x2) ?_
      rw [e, map_add, hq, gL_a0L_of_mem fibT_two_mem]
    have hc : Commute (x2 * repPoint 1 * x2⁻¹) (fibT 2) := by
      rw [commute_iff_eq]
      rw [mul_inv_eq_iff_eq_mul] at hfix
      exact hfix.symm
    exact hc.map SemidirectProduct.inl

end CFSG.Monster.B.E6.StdF4
