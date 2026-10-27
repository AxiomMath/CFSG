module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentLocal
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentConn
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFull

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

theorem rootInv_mem_groupJ :
    rootInv ∈ groupJ.subgroupOf stdGroup :=
  Subgroup.mem_subgroupOf.2 tZ_mem_groupJ

section Root

variable {v u : CVert} {ρ : vStab u →* GStar} {iu : cgraph.neighborSet u ≃ rootClass}
  {c : vStab u}

theorem mem_rootOrbit_iff
    (h : IsCompatLocal u ρ iu) (hc : (c : Shat) = clabelS v)
    (hρc : ρ c = betaStarElt) (hRC : (vStab v).subgroupOf (vStab u) = Subgroup.centralizer {c})
    {z₀ : CVert} (hz₀ : z₀ ∈ cgraph.neighborSet u) (ht : (iu ⟨z₀, hz₀⟩ : stdGroup) = rootInv)
    {z : CVert} (hz : z ∈ cgraph.neighborSet u) :
    (∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = z) ↔
      ∃ j ∈ groupJ.subgroupOf stdGroup, (iu ⟨z, hz⟩ : stdGroup) = j * rootInv * j⁻¹ := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgu : g ∈ vStab u := (Subgroup.mem_inf.1 hg).2
    have hγ : ρ ⟨g, hgu⟩ ∈
        CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed := by
      rw [← CFSG.Monster.B.E6.FieldInvF4.centralizer_betaStarElt, ← range_rho_pair h hc hρc hRC]
      exact ⟨⟨g, hg⟩, rfl⟩
    have key := inl_iv_cvMul h hgu hz₀
    rw [ht, conj_inl_of_mem_starSub hγ rootInv_mem_groupJ] at key
    have hl : (ρ ⟨g, hgu⟩).left ∈ groupJ.subgroupOf stdGroup := hγ
    refine ⟨(ρ ⟨g, hgu⟩).left⁻¹, Subgroup.inv_mem _ hl, ?_⟩
    rw [inv_inv]
    exact SemidirectProduct.inl_injective key
  · rintro ⟨j, hj, hjz⟩
    have hγ : (SemidirectProduct.inl j⁻¹ : GStar) ∈ Subgroup.centralizer {betaStarElt} :=
      Subgroup.mem_centralizer_singleton_iff.2
        (commute_betaStarElt_of_mem_jStar ⟨j⁻¹, Subgroup.inv_mem _ hj, rfl⟩)
    rw [← range_rho_pair h hc hρc hRC] at hγ
    refine hγ.elim (fun x hx => ?_)
    have hxu : (x : Shat) ∈ vStab u := (Subgroup.mem_inf.1 x.2).2
    have key := inl_iv_cvMul h hxu hz₀
    have hx' : ρ ⟨(x : Shat), hxu⟩ = SemidirectProduct.inl j⁻¹ := hx
    rw [ht, hx', ← hom_conj_eq, inv_inv, ← hjz] at key
    have e := iu.injective (Subtype.ext (SemidirectProduct.inl_injective key))
    exact ⟨x, x.2, congrArg Subtype.val e⟩

theorem cvMul_eq_of_mem_rootOrbit (h : IsCompatLocal u ρ iu) (hρc : ρ c = betaStarElt)
    {z : CVert} (hz : z ∈ cgraph.neighborSet u)
    (hJ : ∃ j ∈ groupJ.subgroupOf stdGroup, (iu ⟨z, hz⟩ : stdGroup) = j * rootInv * j⁻¹) :
    cvMul z (c : Shat) = z := by
  obtain ⟨j, hj, hjz⟩ := hJ
  have hmem : (SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup) : GStar) ∈ jStar := by
    rw [hjz]
    exact ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hj rootInv_mem_groupJ)
      (Subgroup.inv_mem _ hj), rfl⟩
  refine (cvMul_eq_self_iff h c.2 hz).2 ?_
  have e : ρ ⟨(c : Shat), c.2⟩ = betaStarElt := hρc
  rw [e]
  exact (commute_betaStarElt_of_mem_jStar hmem).symm

end Root

private theorem ncard_neighborSet
    (u : CVert) : (cgraph.neighborSet u).ncard = 3968055 := by
  rw [← Nat.card_coe_set_eq, natCard_neighborSet_eq, natCard_neighborSet_cv0_eq]

theorem eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {a x : G} (ha : orderOf a = 2)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a :=
  (Short.mem_zpowers_iff_of_orderOf_eq_two ha).1 hx

theorem native_distance_three_pair_two_local_root_orbits
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    (cgraph.induce (cgraph.neighborSet u)).Connected ∧
    (cgraph.neighborSet u ∩ sphereFour v).Nonempty ∧
    (cgraph.neighborSet u \ sphereFour v).Nonempty ∧
    (∀ g ∈ vStab v ⊓ vStab u, ∀ x ∈ cgraph.neighborSet u ∩ sphereFour v,
      cvMul x g ∈ cgraph.neighborSet u ∩ sphereFour v) ∧
    (∀ x ∈ cgraph.neighborSet u ∩ sphereFour v, ∀ x' ∈ cgraph.neighborSet u ∩ sphereFour v,
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul x s = x') ∧
    (∀ g ∈ vStab v ⊓ vStab u, ∀ y ∈ cgraph.neighborSet u \ sphereFour v,
      cvMul y g ∈ cgraph.neighborSet u \ sphereFour v) ∧
    (∀ y ∈ cgraph.neighborSet u \ sphereFour v, ∀ y' ∈ cgraph.neighborSet u \ sphereFour v,
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul y s = y') ∧
    (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
    (cgraph.neighborSet u \ sphereFour v).ncard = 69615 ∧
    (∃ (hc : clabelS v ∈ vStab u) (ρ : vStab u →* GStar)
        (iu : cgraph.neighborSet u ≃ rootClass),
      IsCompatLocal u ρ iu ∧ ρ ⟨clabelS v, hc⟩ = betaStarElt ∧
      (ρ.comp (Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab u ≤ vStab u))).range =
        Subgroup.centralizer {betaStarElt} ∧
      (∀ z : cgraph.neighborSet u, ((z : CVert) ∈ sphereFour v ↔ cvMul z (clabelS v) ≠ z)) ∧
      ∀ z : cgraph.neighborSet u, ((z : CVert) ∉ sphereFour v ↔
        ∃ j ∈ groupJ.subgroupOf stdGroup, (iu z : stdGroup) = j * rootInv * j⁻¹)) ∧
    {z | z ∈ cgraph.neighborSet u ∧ cvMul z (clabelS v) = z} =
      cgraph.neighborSet u \ sphereFour v ∧
    ∀ w : CVert, (cgraph.induce (cgraph.neighborSet w)).Connected := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  have huv : cgraph.dist u v = 3 := by rw [SimpleGraph.dist_comm]; exact hvu
  have hvu' : u ∈ sphereDistThree v := mem_sphereDistThree.2 hvu
  have hN2 := native_distance_three_pair_is_full_local_centralizer hL hO hP hT hvu
  have hRcard : Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = 13244506413465600 :=
    hN2.elim (fun _ h => h.2.2.2.2.1)
  have hXcard : (xSet v u).ncard = 3898440 := hN2.elim (fun _ h => h.2.2.2.2.2.1)
  have hPvu := hP.2.2 v u hvu'
  have hLuv := hL u v huv
  have hcu : clabelS v ∈ vStab u := hLuv.1
  have hsv : clabelS u ∈ vStab v := hLuv.2.1
  have hex : ∃ c : vStab u, (c : Shat) = clabelS v := ⟨⟨clabelS v, hcu⟩, rfl⟩
  refine hex.elim (fun c hc => ?_)
  have hc2 := orderOf_sLabel c hc
  refine (exists_compat_beta hO hP hT huv c hc).elim (fun ρ h₀ => h₀.elim (fun iu h₁ => ?_))
  have h := h₁.1
  have hρc := h₁.2
  have hk := ker_eq_zpowers_cStab h.2.1
  have hC := natCard_centralizer_s h.1 hk hρc hc2
  have hidx := relIndex_le_102 hP hT (mem_sphereDistThree.2 huv) c hc hC
  have hRC := subgroupOf_eq_centralizer h.1 hk hρc hc2 hc hidx hsv
  have hex0 : ∃ z₀ : CVert, ∃ hz₀ : z₀ ∈ cgraph.neighborSet u,
      (iu ⟨z₀, hz₀⟩ : stdGroup) = rootInv :=
    ⟨_, (iu.symm ⟨rootInv, IsConj.refl _⟩).2, by
      rw [Subtype.coe_eta, Equiv.apply_symm_apply]⟩
  refine hex0.elim (fun z₀ hz => hz.elim (fun hz₀ ht => ?_))
  have hstab := natCard_stab_root hsv h hc hρc hRC hz₀ ht
  have horb := natCard_subgroup_eq_mul (vStab v ⊓ vStab u) z₀
  rw [hRcard, hstab] at horb
  have hYcard : {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x}.ncard = 69615 := by omega
  have hYsub : {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} ⊆ cgraph.neighborSet u := by
    rintro _ ⟨g, hg, rfl⟩
    exact cvMul_mem_neighborSet (Subgroup.mem_inf.1 hg).2 hz₀
  have hXinv : ∀ g ∈ vStab v ⊓ vStab u, ∀ x ∈ cgraph.neighborSet u ∩ sphereFour v,
      cvMul x g ∈ cgraph.neighborSet u ∩ sphereFour v := fun g hg x hx =>
    ⟨cvMul_mem_neighborSet (Subgroup.mem_inf.1 hg).2 hx.1,
      mem_sphereFour_of_cvMul (mem_vStab.1 (Subgroup.mem_inf.1 hg).1) hx.2⟩
  have hXtr : ∀ x ∈ cgraph.neighborSet u ∩ sphereFour v,
      ∀ x' ∈ cgraph.neighborSet u ∩ sphereFour v,
        ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul x s = x' := hPvu.2.1
  have hdisj : ∀ z ∈ cgraph.neighborSet u ∩ sphereFour v,
      z ∉ {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} := by
    intro z hzX hzY
    have hsub : cgraph.neighborSet u ∩ sphereFour v ⊆
        {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} := by
      intro x hx
      refine hzY.elim (fun g hg => ?_)
      refine (hXtr z hzX x hx).elim (fun s hs => ?_)
      refine ⟨g * s, Subgroup.mul_mem _ hg.1 (Subgroup.mem_inf.2 ⟨hs.1, hs.2.1⟩), ?_⟩
      rw [cvMul_mul, hg.2, hs.2.2]
    have hle := Set.ncard_le_ncard hsub
    rw [show (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 from hXcard, hYcard] at hle
    omega
  have hunion : cgraph.neighborSet u ∩ sphereFour v ∪
      {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} = cgraph.neighborSet u := by
    refine Set.eq_of_subset_of_ncard_le (Set.union_subset Set.inter_subset_left hYsub) ?_
      (Set.toFinite _)
    rw [Set.ncard_union_eq (Set.disjoint_left.2 hdisj),
      show (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 from hXcard, hYcard,
      ncard_neighborSet]
  have hYeq : cgraph.neighborSet u \ sphereFour v =
      {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} := by
    ext z
    constructor
    · rintro ⟨hzu, hz4⟩
      have hz : z ∈ cgraph.neighborSet u ∩ sphereFour v ∪
          {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} := by
        rw [hunion]; exact hzu
      exact hz.resolve_left fun h' => hz4 h'.2
    · intro hzY
      exact ⟨hYsub hzY, fun hz4 => hdisj z ⟨hYsub hzY, hz4⟩ hzY⟩
  have hc' : (⟨clabelS v, hcu⟩ : vStab u) = c := Subtype.ext hc.symm
  have hfixY : ∀ z ∈ cgraph.neighborSet u \ sphereFour v, cvMul z (clabelS v) = z := by
    intro z hzY
    rw [hYeq] at hzY
    have hJ := (mem_rootOrbit_iff h hc hρc hRC hz₀ ht (hYsub hzY)).1 hzY
    have := cvMul_eq_of_mem_rootOrbit h hρc (hYsub hzY) hJ
    rwa [hc] at this
  have hfixX : ∀ z ∈ cgraph.neighborSet u ∩ sphereFour v, cvMul z (clabelS v) ≠ z := by
    intro z hzX hzc
    have hall : ∀ x ∈ cgraph.neighborSet u, cvMul x (clabelS v) = x := by
      intro x hx
      by_cases hx4 : x ∈ sphereFour v
      · refine (hXtr z hzX x ⟨hx, hx4⟩).elim (fun s hs => ?_)
        have hcomm : Commute s (clabelS v) := commute_clabelS_of_mem_vStab hs.1
        rw [← hs.2.2, ← cvMul_mul, hcomm.eq, cvMul_mul, hzc]
      · exact hfixY x ⟨hx, hx4⟩
    have hmem := (fix_neighborSet_iff u (clabelS v)).1 ⟨hcu, hall⟩
    rw [← coe_clabelS] at hmem
    have hmem' : clabelS v ∈ Subgroup.zpowers (clabelS u) :=
      (mem_zpowers_subtype_iff (clabelS u) (clabelS v)).2 hmem
    rcases eq_one_or_eq_of_mem_zpowers_two (orderOf_clabelS u) hmem' with e | e
    · have h2 := orderOf_clabelS v
      rw [e, orderOf_one] at h2
      exact absurd h2 (by decide)
    · exact hLuv.2.2.1.symm e.symm
  have hFix : {z | z ∈ cgraph.neighborSet u ∧ cvMul z (clabelS v) = z} =
      cgraph.neighborSet u \ sphereFour v := by
    ext z
    constructor
    · rintro ⟨hzu, hzc⟩
      exact ⟨hzu, fun hz4 => hfixX z ⟨hzu, hz4⟩ hzc⟩
    · intro hzY
      exact ⟨hzY.1, hfixY z hzY⟩
  refine ⟨induce_neighborSet_connected u, (hPvu.1), ⟨z₀, ?_⟩, hXinv, hXtr, ?_, ?_, hXcard,
    by rw [hYeq]; exact hYcard, ⟨hcu, ρ, iu, h, by rw [hc']; exact hρc,
      range_rho_pair h hc hρc hRC, ?_, ?_⟩, hFix, induce_neighborSet_connected⟩
  · rw [hYeq]
    exact ⟨1, Subgroup.one_mem _, cvMul_one z₀⟩
  · intro g hg y hy
    rw [hYeq] at hy ⊢
    refine hy.elim (fun g₁ hg₁ => ⟨g₁ * g, Subgroup.mul_mem _ hg₁.1 hg, ?_⟩)
    rw [cvMul_mul, hg₁.2]
  · intro y hy y' hy'
    rw [hYeq] at hy hy'
    refine hy.elim (fun g₁ hg₁ => hy'.elim (fun g₂ hg₂ => ⟨g₁⁻¹ * g₂, ?_, ?_, ?_⟩))
    · exact mem_vStab.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hg₁.1).1)
        (Subgroup.mem_inf.1 hg₂.1).1)
    · exact mem_vStab.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hg₁.1).2)
        (Subgroup.mem_inf.1 hg₂.1).2)
    · rw [← hg₁.2, ← cvMul_mul, mul_inv_cancel_left, hg₂.2]
  · intro z
    constructor
    · intro hz4 hzc
      exact hfixX z ⟨z.2, hz4⟩ hzc
    · intro hzc
      by_contra hz4
      exact hzc (hfixY z ⟨z.2, hz4⟩)
  · intro z
    have hiff := mem_rootOrbit_iff h hc hρc hRC hz₀ ht z.2
    constructor
    · intro hz4
      have hzY : (z : CVert) ∈ cgraph.neighborSet u \ sphereFour v := ⟨z.2, hz4⟩
      rw [hYeq] at hzY
      exact hiff.1 hzY
    · intro hJ
      have hzY : (z : CVert) ∈ {x | ∃ g ∈ vStab v ⊓ vStab u, cvMul z₀ g = x} := hiff.2 hJ
      rw [← hYeq] at hzY
      exact hzY.2

end CFSG.Monster.B.TwoA.Amalgam
