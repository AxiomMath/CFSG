module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.Monster.B.E6.StdF4Weyl
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.Classical CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem le_e6HighestRoot
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (i : Fin TwistTag.E6.tag.rank) : α i ≤ e6HighestRoot i := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      (List.finRange TwistTag.E6.tag.rank).all fun i =>
        decide (TwistTag.E6.tag.rootCertificate.root k i ≤ e6HighestRoot i) := by decide
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, decide_eq_true_eq,
    forall_const] at h
  exact h k hk i

theorem eq_e6HighestRoot_of_height {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (h : height α = 11) : α = e6HighestRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have hl : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.E6.tag.rootCertificate.root k) = 11 →
        TwistTag.E6.tag.rootCertificate.root k = e6HighestRoot) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hl
  exact hl k hk h

@[expose] def theta : Fin Tag.E6.rank → ℤ := e6HighestRoot

theorem theta_eq : theta = e6HighestRoot := rfl

theorem cartan_theta (i : Fin Tag.E6.rank) :
    ∑ j, Tag.E6.cartan i j * theta j = if (i : ℕ) = 1 then 1 else 0 := by
  revert i
  decide

theorem isRoot_theta : IsRoot Tag.E6 theta := isRoot_e6HighestRoot

theorem height_theta : height theta = 11 := height_e6HighestRoot

theorem toLat_theta : toLat E6Folded.θ = theta := rfl

@[expose] def rootInvM :
    ModGL Tag.E6 K := pinnedX Tag.E6 K theta 1

theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem betaGL_rootInvM :
    betaGL rootInvM = rootInvM :=
  Units.ext (by rw [betaGL_apply, rootInvM, entrywise_pinnedX, map_one])

theorem rootInvM_mem_posUnipotent :
    rootInvM ∈ posUnipotent Tag.E6 K :=
  pinnedX_e6HighestRoot_mem_posUnipotent 1

theorem twistHom_rootInvM :
    twistHom TwistTag.E6 K (RingHom.id K) rootInvM = rootInvM := by
  have h := twistHom_id_pinnedX (t := TwistTag.E6) two_eq_zero_K isRoot_e6HighestRoot (1 : K)
  rw [permLattice_e6HighestRoot] at h
  exact h

theorem rootInvM_mem_stdGroup :
    rootInvM ∈ stdGroup := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    ⟨rootInvM_mem_posUnipotent, ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
    ⟨pinnedX_mem_adjointGroup _ _, ?_⟩
  rw [twistHom_eq_conj, betaGL_rootInvM, ← C2E6Std.twistHom_id_eq, twistHom_rootInvM]

@[expose] def rootInv :
    stdGroup := ⟨rootInvM, rootInvM_mem_stdGroup⟩

theorem coe_rootInv :
    (rootInv : ModGL Tag.E6 K) = rootInvM := rfl

theorem rootInvM_mul_self :
    rootInvM * rootInvM = 1 := by
  rw [rootInvM, ← pinnedX_add, one_add_one_eq_two, two_eq_zero_K, pinnedX_zero]

theorem rootInvM_ne_one :
    rootInvM ≠ 1 := by
  intro h
  rw [rootInvM, ← pinnedX_zero Tag.E6 K theta] at h
  exact one_ne_zero ((pinnedX_injective (τ := Tag.E6) (R := K) theta) h)

theorem rootInv_mul_self :
    rootInv * rootInv = 1 := Subtype.ext rootInvM_mul_self

theorem rootInv_ne_one :
    rootInv ≠ 1 := by
  intro h
  apply rootInvM_ne_one
  rw [← coe_rootInv, h, OneMemClass.coe_one]

theorem orderOf_rootInv :
    orderOf rootInv = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, rootInv_mul_self]) rootInv_ne_one

theorem betaG_rootInv :
    betaG rootInv = rootInv := Subtype.ext betaGL_rootInvM

theorem apply_rootInv_of_mem_betaGroup
    (b : betaGroup) :
    (b : MulAut stdGroup) rootInv = rootInv := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact betaG_rootInv

theorem commute_torusElt_rootInvM
    {i : Fin Tag.E6.rank} (hi : (i : ℕ) ≠ 1) (s : Kˣ) :
    torusElt Tag.E6 K i s * rootInvM = rootInvM * torusElt Tag.E6 K i s := by
  have h := root_torus_conjugation (R := K) i isRoot_theta s 1
  have hc := cartan_theta i
  rw [ite_eq_right hi] at hc
  rw [hc, zpow_zero, Units.val_one, one_mul] at h
  rw [rootInvM, ← mul_inv_eq_iff_eq_mul, h]

theorem fixedTorusGen_mem_centralizer :
    fixedTorusGen ∈ Subgroup.centralizer {rootInvM} := by
  rw [Subgroup.mem_centralizer_singleton_iff, fixedTorusGen, mul_assoc,
    commute_torusElt_rootInvM (i := i6 4) (by decide), ← mul_assoc,
    commute_torusElt_rootInvM (i := i6 2) (by decide), mul_assoc]

theorem stdBorel_le_centralizer :
    stdBorel ≤ Subgroup.centralizer {rootInvM} := by
  rw [show stdBorel = _ from graphFixedRootBorel_eq_sup C2E6Std.barHom_surjective]
  refine sup_le ?_ ?_
  · intro h hh
    have hh' : h ∈ stdTorus0 := stdTorus0_eq_stdTorus ▸ hh
    rw [stdTorus0_eq_zpowers] at hh'
    exact (Subgroup.zpowers_le.mpr fixedTorusGen_mem_centralizer) hh'
  · intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_e6HighestRoot_of_mem_posUnipotent K hu.1 1).eq

theorem nativeRep_mem_centralizer
    {i : Fin 4} (hi : i ∈ firstJ) :
    nativeRep i ∈ Subgroup.centralizer {rootInvM} := by
  have hfix : nativeRefl i • theta = theta := by
    have h := wsmul_simple i E6Folded.θ
    have hθ : E6Folded.r i E6Folded.θ = E6Folded.θ :=
      congrArg Subtype.val (E6Folded.gen_θΛ (j := i) hi)
    rw [hθ] at h
    unfold wsmul at h
    rw [nativeCoxeterSystem_simple, coe_nativeSimple_eq_nativeRefl] at h
    exact h
  have h := canonicalRep_mul_pinnedX_mul_inv_of_two two_eq_zero_K (nativeRefl i)
    isRoot_theta (1 : K)
  rw [hfix] at h
  rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul]
  exact h

theorem nativeParabolic_firstJ_le_centralizer :
    nativeParabolic firstJ ≤ Subgroup.centralizer {rootInvM} := by
  refine (Subgroup.closure_le _).2 (Set.union_subset (fun b hb => stdBorel_le_centralizer hb) ?_)
  rintro _ ⟨i, hi, rfl⟩
  exact nativeRep_mem_centralizer hi

theorem foldedIndex_bijective : Function.Bijective foldedIndex :=
  Fin.rev_bijective

theorem exists_eq_nativeParabolic
    {A : Subgroup (ModGL Tag.E6 K)} (hB : stdBorel ≤ A)
    (hA : A ≤ stdGroup) : ∃ I : Set (Fin 4), A = nativeParabolic I := by
  have h := (fixed_Borel_overgroup_classification TwistTag.E6 K C2E6Std.barEquiv A
    (by rwa [C2E6Std.barEquiv_toRingHom]) (by rwa [C2E6Std.barEquiv_toRingHom])).1
  rw [C2E6Std.barEquiv_toRingHom] at h
  refine ⟨foldedIndex ⁻¹' {a | canonicalRep (coxeterSystem TwistTag.E6.tag) K
    (TwistTag.E6.orbitReflection a) ∈ A}, ?_⟩
  rw [nativeParabolic_eq, Set.image_preimage_eq _ foldedIndex_bijective.2]
  exact h

theorem nativeRep_mem_nativeParabolic_iff
    (I : Set (Fin 4)) (i : Fin 4) :
    nativeRep i ∈ nativeParabolic I ↔ i ∈ I := by
  have h := (fixed_standard_parabolic_cells TwistTag.E6 K C2E6Std.barEquiv).2.2.1
    (foldedIndex '' I) (foldedIndex i)
  rw [C2E6Std.barEquiv_toRingHom] at h
  rw [nativeParabolic_eq, nativeRep, nativeRefl_eq]
  exact h.trans (foldedIndex_bijective.1.mem_set_image)

theorem nativeParabolic_univ :
    nativeParabolic Set.univ = stdGroup := by
  have h := (fixed_standard_parabolic_cells TwistTag.E6 K C2E6Std.barEquiv).2.2.2.2.2
  rw [C2E6Std.barEquiv_toRingHom] at h
  rw [nativeParabolic_eq, Set.image_univ_of_surjective foldedIndex_bijective.2]
  exact h

theorem center_stdGroup :
    Subgroup.center stdGroup = ⊥ := by
  have h := exceptional_fixed_center_trivial TwistTag.E6 K C2E6Std.barEquiv
  rw [C2E6Std.barEquiv_toRingHom] at h
  exact h

theorem centralizer_inf_stdGroup :
    Subgroup.centralizer {rootInvM} ⊓ stdGroup = nativeParabolic firstJ := by
  have hPJ := nativeParabolic_firstJ_le_centralizer
  have hle : nativeParabolic firstJ ≤ Subgroup.centralizer {rootInvM} ⊓ stdGroup :=
    le_inf hPJ (nativeParabolic_le_stdGroup firstJ)
  obtain ⟨I, hI⟩ := exists_eq_nativeParabolic
    ((stdBorel_le_nativeParabolic firstJ).trans hle) inf_le_right
  have hJI : firstJ ⊆ I := fun i hi => by
    rw [← nativeRep_mem_nativeParabolic_iff, ← hI]
    exact hle (Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩))
  by_cases h0 : (0 : Fin 4) ∈ I
  · exfalso
    have hIu : I = Set.univ := Set.eq_univ_of_forall fun i => by
      rcases fin4_cases i with rfl | rfl | rfl | rfl
      · exact h0
      all_goals exact hJI (by simp [firstJ])
    rw [hIu, nativeParabolic_univ] at hI
    have hcen : rootInv ∈ Subgroup.center stdGroup := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : ModGL Tag.E6 K) ∈ Subgroup.centralizer {rootInvM} ⊓ stdGroup := by
        rw [hI]
        exact g.2
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_rootInv]
      exact Subgroup.mem_centralizer_singleton_iff.1 hg.1
    rw [center_stdGroup, Subgroup.mem_bot] at hcen
    exact rootInv_ne_one hcen
  · have hIJ : I = firstJ := Set.Subset.antisymm (fun i hi => by
      rcases fin4_cases i with rfl | rfl | rfl | rfl
      · exact absurd hi h0
      all_goals simp [firstJ]) hJI
    rw [hI, hIJ]

theorem centralizer_rootInv :
    Subgroup.centralizer {rootInv} = (nativeParabolic firstJ).subgroupOf stdGroup := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← centralizer_inf_stdGroup, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← coe_rootInv,
    ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  exact ⟨fun h => ⟨congrArg Subtype.val h, g.2⟩, fun h => Subtype.ext h.1⟩

theorem mem_centralizer_rootInv_iff
    (g : stdGroup) :
    g * rootInv * g⁻¹ = rootInv ↔ (g : ModGL Tag.E6 K) ∈ nativeParabolic firstJ := by
  rw [← Subgroup.mem_subgroupOf, ← centralizer_rootInv, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]

@[expose] def rootStar :
    GStar := SemidirectProduct.inl rootInv

theorem conj_inl
    (γ : GStar) (x : stdGroup) :
    γ * SemidirectProduct.inl x * γ⁻¹ =
      SemidirectProduct.inl (γ.left * (γ.right : MulAut stdGroup) x * γ.left⁻¹) := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, Subgroup.coe_subtype, map_one,
      MulAut.one_apply, map_inv, mul_assoc]
    congr 2
    rw [map_mul, map_inv, MulAut.apply_inv_self]
  · simp

theorem conj_rootStar
    (γ : GStar) :
    γ * rootStar * γ⁻¹ = SemidirectProduct.inl (γ.left * rootInv * γ.left⁻¹) := by
  rw [rootStar, conj_inl, apply_rootInv_of_mem_betaGroup]

theorem centralizer_rootStar :
    Subgroup.centralizer {rootStar} = parStar firstJ := by
  ext γ
  rw [mem_parStar, Subgroup.mem_centralizer_singleton_iff, ← mem_centralizer_rootInv_iff,
    ← mul_inv_eq_iff_eq_mul, conj_rootStar]
  exact SemidirectProduct.inl_injective.eq_iff

theorem setOf_isConj_rootStar :
    {y : GStar | IsConj rootStar y} =
      SemidirectProduct.inl '' {x : stdGroup | IsConj rootInv x} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, isConj_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, ⟨γ.left, rfl⟩, (conj_rootStar γ).symm⟩
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ?_⟩
    rw [conj_rootStar]
    rfl

end CFSG.Monster.B.E6.StdF4
