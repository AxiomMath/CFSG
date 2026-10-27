module

public import CFSG.Monster.B.GSide.IndexTwoExtension
public import CFSG.Monster.B.TwoA.Amalgam.NativeChainFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8

theorem commute_clabel_iff
    (v : CVert) (s : Shat) :
    (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v :=
  native_global_label_bijection_and_full_vertex_centralizer.2.2.2.1 v s

abbrev cEdgeFix :
    Subgroup Shat := vStab cv0 ⊓ vStab cw0

abbrev cEdgeStab :
    Subgroup Shat := cvSetStab {cv0, cw0}

theorem exists_edge_swap :
    ∃ s : Shat, cvMul cv0 s = cw0 ∧ cvMul cw0 s = cv0 :=
  cvMul_edge_transitive cgraph_adj_cv0_cw0 cgraph_adj_cv0_cw0.symm

theorem cEdgeFix_le_cEdgeStab :
    cEdgeFix ≤ cEdgeStab := fun _ hg =>
  (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).2 (Or.inl ⟨hg.1, hg.2⟩)

@[expose] def cEdgeIncl :
    cEdgeFix →* cEdgeStab := Subgroup.inclusion cEdgeFix_le_cEdgeStab

theorem coe_cEdgeIncl
    (a : cEdgeFix) : ((cEdgeIncl a : cEdgeStab) : Shat) = a := rfl

theorem cEdgeIncl_injective :
    Function.Injective cEdgeIncl := Subgroup.inclusion_injective _

theorem cEdgeIncl_range :
    cEdgeIncl.range = cEdgeFix.subgroupOf cEdgeStab :=
  Subgroup.inclusion_range _

theorem swap_mem_cEdgeStab
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    s ∈ cEdgeStab :=
  (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).2 (Or.inr ⟨hs0, hs1⟩)

theorem cEdgeStab_eq_sup
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    cEdgeStab = cEdgeFix ⊔ Subgroup.zpowers s := by
  apply le_antisymm
  · intro g hg
    rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Subgroup.mem_sup_left ⟨h0, h1⟩
    · have hgs : g * s ∈ cEdgeFix := Subgroup.mem_inf.2
        ⟨by rw [mem_vStab, cvMul_mul, h0, hs1], by rw [mem_vStab, cvMul_mul, h1, hs0]⟩
      have h := (cEdgeFix ⊔ Subgroup.zpowers s).mul_mem (Subgroup.mem_sup_left hgs)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers s)))
      rwa [mul_inv_cancel_right] at h
  · exact sup_le cEdgeFix_le_cEdgeStab (Subgroup.zpowers_le.2 (swap_mem_cEdgeStab hs0 hs1))

theorem swap_mul_self_mem
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    s * s ∈ cEdgeFix := Subgroup.mem_inf.2
  ⟨by rw [mem_vStab, cvMul_mul, hs0, hs1], by rw [mem_vStab, cvMul_mul, hs1, hs0]⟩

@[expose] def swapE
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    cEdgeStab :=
  ⟨s, swap_mem_cEdgeStab hs0 hs1⟩

theorem coe_swapE
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    (swapE hs0 hs1 : Shat) = s := rfl

theorem swapE_not_mem_range
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    swapE hs0 hs1 ∉ cEdgeIncl.range := by
  rintro ⟨a, ha⟩
  have h : (a : Shat) = s := congrArg Subtype.val ha
  have h0 : cvMul cv0 (a : Shat) = cv0 := a.2.1
  rw [h, hs0] at h0
  exact cgraph_adj_cv0_cw0.ne h0.symm

theorem cEdgeFix_index :
    (cEdgeFix.subgroupOf cEdgeStab).index = 2 := by
  obtain ⟨s, hs0, hs1⟩ := exists_edge_swap
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨swapE hs0 hs1, fun h => ?_, fun b => ?_⟩
  · have h0 : cvMul cv0 s = cv0 := (Subgroup.mem_subgroupOf.1 h).1
    rw [hs0] at h0
    exact cgraph_adj_cv0_cw0.ne h0.symm
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 b.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · refine Or.inl (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · rw [mem_vStab, Subgroup.coe_mul, cvMul_mul, h0]
        exact hs1
      · rw [mem_vStab, Subgroup.coe_mul, cvMul_mul, h1]
        exact hs0

theorem index_range_cEdgeIncl :
    cEdgeIncl.range.index = 2 := by
  rw [cEdgeIncl_range]
  exact cEdgeFix_index

theorem clabel_cw0 :
    clabel cw0 = cQ * xhat := by
  rw [cw0, clabel_nbr]
  simp

theorem mem_cEdgeFix_iff
    {g : Shat} : g ∈ cEdgeFix ↔ (g : Dfull) ∈ Pc 0 := by
  rw [← Eam_inf_centralizer_xhat, Subgroup.mem_inf, Subgroup.mem_inf, mem_vStab_cv0, mem_vStab,
    ← commute_clabel_iff, clabel_cw0, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hg => ?_
  have hc : (g : Dfull) * cQ = cQ * g :=
    Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hg)
  constructor
  · intro h
    refine mul_left_cancel (a := cQ) ?_
    calc cQ * ((g : Dfull) * xhat) = g * (cQ * xhat) := by simp only [← mul_assoc, hc]
      _ = cQ * xhat * g := h
      _ = cQ * (xhat * g) := mul_assoc _ _ _
  · intro h
    calc (g : Dfull) * (cQ * xhat) = cQ * (g * xhat) := by simp only [← mul_assoc, hc]
      _ = cQ * (xhat * g) := by rw [h]
      _ = cQ * xhat * g := (mul_assoc _ _ _).symm

theorem clabelS_cv0_mem_cEdgeFix :
    clabelS cv0 ∈ cEdgeFix :=
  ⟨(commute_clabel_iff cv0 _).1 rfl,
    (commute_clabel_iff cw0 _).1 (clabel_adj cgraph_adj_cv0_cw0).2.1⟩

theorem clabelS_cw0_mem_cEdgeFix :
    clabelS cw0 ∈ cEdgeFix :=
  ⟨(commute_clabel_iff cv0 _).1 (clabel_adj cgraph_adj_cv0_cw0).2.1.symm,
    (commute_clabel_iff cw0 _).1 rfl⟩

@[expose] def lamV0 :
    cEdgeFix := ⟨clabelS cv0, clabelS_cv0_mem_cEdgeFix⟩

@[expose] def lamW0 :
    cEdgeFix := ⟨clabelS cw0, clabelS_cw0_mem_cEdgeFix⟩

theorem coe_lamV0 :
    ((lamV0 : Shat) : Dfull) = cQ := clabel_cv0

theorem coe_lamW0 :
    ((lamW0 : Shat) : Dfull) = cQ * xhat := clabel_cw0

theorem ext_cEdgeFix
    {a b : cEdgeFix} (h : ((a : Shat) : Dfull) = ((b : Shat) : Dfull)) :
    a = b :=
  Subtype.ext (Subtype.ext h)

theorem lamV0_ne_lamW0 :
    lamV0 ≠ lamW0 := fun h =>
  (clabel_adj cgraph_adj_cv0_cw0).1 (congrArg (fun x : cEdgeFix => ((x : Shat) : Dfull)) h)

theorem lamV0_ne_one :
    lamV0 ≠ 1 := fun h =>
  cQ_ne_one (coe_lamV0.symm.trans (congrArg (fun x : cEdgeFix => ((x : Shat) : Dfull)) h))

theorem lamW0_ne_one :
    lamW0 ≠ 1 := fun h => by
  have h1 : cQ * xhat = 1 :=
    coe_lamW0.symm.trans (congrArg (fun x : cEdgeFix => ((x : Shat) : Dfull)) h)
  have h2 : xhat = cQ :=
    calc xhat = cQ * (cQ * xhat) := by rw [← mul_assoc, cQ_mul_self, one_mul]
      _ = cQ := by rw [h1, mul_one]
  exact cQ_ne_xhat h2.symm

theorem lamV0_mul_self :
    lamV0 * lamV0 = 1 :=
  ext_cEdgeFix (clabel_adj cgraph_adj_cv0_cw0).2.2.1

theorem lamW0_mul_self :
    lamW0 * lamW0 = 1 :=
  ext_cEdgeFix (clabel_adj cgraph_adj_cv0_cw0).2.2.2.1

theorem lamV0_mul_comm :
    lamV0 * lamW0 = lamW0 * lamV0 :=
  ext_cEdgeFix (clabel_adj cgraph_adj_cv0_cw0).2.1

theorem lamV0_mem_center :
    lamV0 ∈ Subgroup.center cEdgeFix :=
  Subgroup.mem_center_iff.2 fun g => ext_cEdgeFix ((commute_clabel_iff cv0 g).2 g.2.1)

theorem lamW0_mem_center :
    lamW0 ∈ Subgroup.center cEdgeFix :=
  Subgroup.mem_center_iff.2 fun g => ext_cEdgeFix ((commute_clabel_iff cw0 g).2 g.2.2)

theorem mem_center_cEdgeFix_iff
    {z : cEdgeFix} :
    z ∈ Subgroup.center cEdgeFix ↔ z = 1 ∨ z = lamV0 ∨ z = lamW0 ∨ z = lamV0 * lamW0 := by
  constructor
  · intro hz
    have hzP : ((z : Shat) : Dfull) ∈ P1 := mem_cEdgeFix_iff.1 z.2
    have hyc : (QuotientGroup.mk (⟨_, hzP⟩ : P1) : P1 ⧸ Subgroup.zpowers cP1) ∈
        Subgroup.center (P1 ⧸ Subgroup.zpowers cP1) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have hgS : (g : Dfull) ∈ Shat := Eam_le_Shat (Pc_le_Eam 0 g.2)
      have hgA : (⟨g, hgS⟩ : Shat) ∈ cEdgeFix := mem_cEdgeFix_iff.2 g.2
      have h := Subgroup.mem_center_iff.1 hz ⟨⟨g, hgS⟩, hgA⟩
      exact Subtype.ext (congrArg (fun x : cEdgeFix => ((x : Shat) : Dfull)) h)
    have hcl := mem_closure_of_center hyc
    rw [← range_kleinHom] at hcl
    obtain ⟨v, hv⟩ := hcl
    have hv' : xhat ^ (Multiplicative.toAdd v).1.val * cQ ^ (Multiplicative.toAdd v).2.val =
        ((z : Shat) : Dfull) := hv
    have h01 : ∀ a : ZMod 2, a.val = 0 ∨ a.val = 1 := fun a => by
      have := ZMod.val_lt a
      omega
    have hxc : xhat * cQ = cQ * xhat := (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm
    rcases h01 (Multiplicative.toAdd v).1 with ha | ha <;>
      rcases h01 (Multiplicative.toAdd v).2 with hb | hb <;>
      simp only [ha, hb, pow_zero, pow_one, one_mul, mul_one] at hv'
    · exact Or.inl (ext_cEdgeFix hv'.symm)
    · exact Or.inr (Or.inl (ext_cEdgeFix (hv'.symm.trans coe_lamV0.symm)))
    · refine Or.inr (Or.inr (Or.inr (ext_cEdgeFix ?_)))
      show ((z : Shat) : Dfull) = ((lamV0 : Shat) : Dfull) * ((lamW0 : Shat) : Dfull)
      rw [coe_lamV0, coe_lamW0, ← mul_assoc, cQ_mul_self, one_mul, ← hv']
    · refine Or.inr (Or.inr (Or.inl (ext_cEdgeFix ?_)))
      rw [coe_lamW0, ← hv', hxc]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact lamV0_mem_center
    · exact lamW0_mem_center
    · exact Subgroup.mul_mem _ lamV0_mem_center lamW0_mem_center

theorem center_cEdgeFix :
    Subgroup.center cEdgeFix = Subgroup.closure {lamV0, lamW0} := by
  apply le_antisymm
  · intro z hz
    rcases mem_center_cEdgeFix_iff.1 hz with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact lamV0_mem_center
    · exact lamW0_mem_center

theorem natCard_center_cEdgeFix :
    Nat.card (Subgroup.center cEdgeFix) = 4 := by
  have e : (Subgroup.center cEdgeFix : Set cEdgeFix) = {1, lamV0, lamW0, lamV0 * lamW0} := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact mem_center_cEdgeFix_iff
  have hp1 : lamV0 * lamW0 ≠ 1 := fun h => lamV0_ne_lamW0 (by
    calc lamV0 = lamV0 * (lamW0 * lamW0) := by rw [lamW0_mul_self, mul_one]
      _ = lamW0 := by rw [← mul_assoc, h, one_mul])
  have hv : lamV0 ≠ lamV0 * lamW0 := fun h =>
    lamW0_ne_one (mul_left_cancel (h.symm.trans (mul_one lamV0).symm))
  have hw : lamW0 ≠ lamV0 * lamW0 := fun h =>
    lamV0_ne_one (mul_right_cancel (h.symm.trans (one_mul lamW0).symm))
  have h1 : (1 : cEdgeFix) ∉ ({lamV0, lamW0, lamV0 * lamW0} : Set cEdgeFix) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨lamV0_ne_one.symm, lamW0_ne_one.symm, hp1.symm⟩
  have h2 : lamV0 ∉ ({lamW0, lamV0 * lamW0} : Set cEdgeFix) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨lamV0_ne_lamW0, hv⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, e, Set.ncard_insert_of_notMem h1,
    Set.ncard_insert_of_notMem h2, Set.ncard_pair hw]

@[expose] def cEdgeSigma
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    cEdgeFix ≃* cEdgeFix where
  toFun a := ⟨s * a * s⁻¹, by
    have h0 : cvMul cw0 s⁻¹ = cv0 := by rw [← hs0, cvMul_inv_cancel]
    have h1 : cvMul cv0 s⁻¹ = cw0 := by rw [← hs1, cvMul_inv_cancel]
    exact Subgroup.mem_inf.2 ⟨by rw [mem_vStab, cvMul_mul, cvMul_mul, hs0, mem_vStab.1 a.2.2, h0],
      by rw [mem_vStab, cvMul_mul, cvMul_mul, hs1, mem_vStab.1 a.2.1, h1]⟩⟩
  invFun a := ⟨s⁻¹ * a * s, by
    have h0 : cvMul cw0 s⁻¹ = cv0 := by rw [← hs0, cvMul_inv_cancel]
    have h1 : cvMul cv0 s⁻¹ = cw0 := by rw [← hs1, cvMul_inv_cancel]
    exact Subgroup.mem_inf.2 ⟨by rw [mem_vStab, cvMul_mul, cvMul_mul, h1, mem_vStab.1 a.2.2, hs1],
      by rw [mem_vStab, cvMul_mul, cvMul_mul, h0, mem_vStab.1 a.2.1, hs0]⟩⟩
  left_inv a := Subtype.ext (show s⁻¹ * (s * (a : Shat) * s⁻¹) * s = a by group)
  right_inv a := Subtype.ext (show s * (s⁻¹ * (a : Shat) * s) * s⁻¹ = a by group)
  map_mul' a b := Subtype.ext (show s * ((a : Shat) * b) * s⁻¹ = s * a * s⁻¹ * (s * b * s⁻¹) by
    group)

theorem coe_cEdgeSigma
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    (a : cEdgeFix) : (cEdgeSigma hs0 hs1 a : Shat) = s * a * s⁻¹ := rfl

theorem cEdgeSigma_spec
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    (a : cEdgeFix) :
    swapE hs0 hs1 * cEdgeIncl a * (swapE hs0 hs1)⁻¹ = cEdgeIncl (cEdgeSigma hs0 hs1 a) :=
  Subtype.ext rfl

theorem cEdgeSigma_lamV0
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    cEdgeSigma hs0 hs1 lamV0 = lamW0 := by
  have h1 : cvMul cv0 s⁻¹ = cw0 := by rw [← hs1, cvMul_inv_cancel]
  have e := clabelS_cvMul cv0 s⁻¹
  rw [h1, inv_inv] at e
  exact Subtype.ext e.symm

theorem cEdgeSigma_lamW0
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    cEdgeSigma hs0 hs1 lamW0 = lamV0 := by
  have h0 : cvMul cw0 s⁻¹ = cv0 := by rw [← hs0, cvMul_inv_cancel]
  have e := clabelS_cvMul cw0 s⁻¹
  rw [h0, inv_inv] at e
  exact Subtype.ext e.symm

theorem cEdge_hnorm
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    ∀ c ∈ Subgroup.center cEdgeFix, cEdgeSigma hs0 hs1 c = c →
      ∃ d ∈ Subgroup.center cEdgeFix, c = d * cEdgeSigma hs0 hs1 d := by
  intro c hc hfix
  rcases mem_center_cEdgeFix_iff.1 hc with rfl | rfl | rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, by rw [map_one, mul_one]⟩
  · rw [cEdgeSigma_lamV0] at hfix
    exact absurd hfix.symm lamV0_ne_lamW0
  · rw [cEdgeSigma_lamW0] at hfix
    exact absurd hfix lamV0_ne_lamW0
  · exact ⟨lamV0, lamV0_mem_center, by rw [cEdgeSigma_lamV0]⟩

theorem exists_hom_cEdgeStab
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    {G : Type*} [Group G] (θ : cEdgeFix →* G) (hθ : Function.Injective θ) (t : G)
    (b : cEdgeFix) (ht : ∀ a, t * θ a * t⁻¹ = θ (cEdgeSigma hs0 hs1 (b * a * b⁻¹)))
    (ht2 : t * t ∈ θ.range) :
    ∃ f : cEdgeStab →* G, (∀ a, f (cEdgeIncl a) = θ a) ∧
      ∃ d ∈ Subgroup.center cEdgeFix, f (swapE hs0 hs1) = t * θ (b⁻¹ * d) :=
  exists_hom_of_index_two cEdgeIncl cEdgeIncl_injective index_range_cEdgeIncl
    (swapE_not_mem_range hs0 hs1) (cEdgeSigma hs0 hs1) (cEdgeSigma_spec hs0 hs1) θ hθ t b ht ht2
    (cEdge_hnorm hs0 hs1)

theorem exists_hom_cEdgeStab'
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    {G : Type*} [Group G] (θ : cEdgeFix →* G) (hθ : Function.Injective θ) (t : G)
    (ht : ∀ a, t * θ a * t⁻¹ = θ (cEdgeSigma hs0 hs1 a)) (ht2 : t * t ∈ θ.range) :
    ∃ f : cEdgeStab →* G, (∀ a, f (cEdgeIncl a) = θ a) ∧
      ∃ d ∈ Subgroup.center cEdgeFix, f (swapE hs0 hs1) = t * θ d :=
  exists_hom_of_index_two' cEdgeIncl cEdgeIncl_injective index_range_cEdgeIncl
    (swapE_not_mem_range hs0 hs1) (cEdgeSigma hs0 hs1) (cEdgeSigma_spec hs0 hs1) θ hθ t ht ht2
    (cEdge_hnorm hs0 hs1)

end CFSG.Monster.B.GSide
