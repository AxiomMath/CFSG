module

public import CFSG.Sporadic.Schreier.LyCover
public import CFSG.Sporadic.Ly.Primitive

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native
open CFSG.Sporadic.SchreierLemmas

theorem lyz_mem_lyC : lyz ∈ lyC := by
  have h := (repW_relResidue 0 1 0).2
  change RepM (relResidue csArr tTab 0 1 0).2 _ at h
  rw [cover_parts.2.2.2.2.2.2.2.2] at h
  have := repM_matA.unique h
  rw [lyz, this]
  exact (FreeGroup.lift cC _).2

@[expose] def zC :
    lyC := ⟨lyz, lyz_mem_lyC⟩

theorem cSeed_eq_cStar (i : Fin 2) : cStar i = cSeed i := by
  fin_cases i
  · exact extendByWords_getD_of_lt _ _ (by simp)
  · exact extendByWords_getD_of_lt _ _ (by simp)

theorem commute_lyz_cSeed
    (i : Fin 2) : lyz * cSeed i = cSeed i * lyz := by
  apply mat_injective
  rw [mat_mul, mat_mul, lyz, mat_a]
  have hc : RepM (pairAt csArr i).1 (cSeed i) := by
    have := (repM_csArr i).1
    rwa [cSeed_eq_cStar i] at this
  have heq : mulM 5 111 matA (pairAt csArr i).1 = mulM 5 111 (pairAt csArr i).1 matA := by
    fin_cases i
    · exact cover_parts.2.2.1
    · exact cover_parts.2.2.2.1
  have := congrArg (toMat 5 111) heq
  rwa [toMat_mulM, toMat_mulM, toMat_matA, hc] at this

theorem zC_mem_center :
    zC ∈ Subgroup.center lyC := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure (Set.range cC) := by rw [closure_cC]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Subtype.ext (commute_lyz_cSeed i).symm
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def zGroup :
    Subgroup lyC := Subgroup.zpowers zC

theorem zGroup_le_center :
    zGroup ≤ Subgroup.center lyC :=
  (Subgroup.zpowers_le).2 zC_mem_center

instance zGroup_normal :
    zGroup.Normal := Subgroup.normal_of_le_center zGroup_le_center

theorem orderOf_zC :
    orderOf zC = 2 := by
  rw [← Subgroup.orderOf_coe, show ((zC : lyC) : J) = a from rfl, orderOf_a]

theorem mem_zGroup
    {g : lyC} : g ∈ zGroup ↔ g = 1 ∨ g = zC := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, orderOf_zC, Nat.cast_ofNat]
    rcases Int.emod_two_eq k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem chain_hsift
    (i : Fin lyChain.baseCount) (x : Fin 11) (hx : x ∈ lyChain.orbit i)
    (j : Fin lyChain.strongCount) (hj : j ∈ lyChain.levelSet pGen i) :
    FreeGroup.lift pGen (lyChain.residue pGen i (lyChain.schreierElement pGen i x j)) = 1 := by
  have h := (repW_relResidue i x j).1
  obtain ⟨h1, -⟩ := rel_parts i x hx j (mem_levelSet.1 hj)
  rw [h1] at h
  exact h.eq repP_id11

theorem chain_hsiftZ
    (i : Fin lyChain.baseCount) (x : Fin 11) (hx : x ∈ lyChain.orbit i)
    (j : Fin lyChain.strongCount) (hj : j ∈ lyChain.levelSet pGen i) :
    FreeGroup.lift cC (lyChain.residue pGen i (lyChain.schreierElement pGen i x j)) ∈
      zGroup := by
  have h := (repW_relResidue i x j).2
  obtain ⟨-, h2⟩ := rel_parts i x hx j (mem_levelSet.1 hj)
  rw [mem_zGroup]
  rcases h2 with h2 | h2
  · rw [h2] at h
    left
    exact Subtype.ext (repM_id.unique h).symm
  · rw [h2] at h
    right
    exact Subtype.ext (repM_matA.unique h).symm

theorem isSimpleGroup_closure_pGen : IsSimpleGroup (Subgroup.closure (Set.range pGen)) :=
  (MulEquiv.subgroupCongr closure_pGen_eq).isSimpleGroup_congr.2
    (alternatingGroup.isSimpleGroup (by simp))

theorem cC_zero_not_mem :
    cC 0 ∉ zGroup := by
  have hc : RepM (pairAt csArr 0).1 (cSeed 0) := by
    have := (repM_csArr (0 : Fin 2)).1
    rw [cSeed_eq_cStar 0] at this
    exact this
  rw [mem_zGroup]
  rintro (h | h)
  · apply toMat_ne_of_diffMod5 cover_parts.2.2.2.2.1
    rw [hc, toMat_idM, ← mat_one]
    exact congrArg mat (congrArg Subtype.val h)
  · apply toMat_ne_of_diffMod5 cover_parts.2.2.2.2.2.1
    rw [hc, toMat_matA, ← mat_a]
    exact congrArg mat (congrArg Subtype.val h)

theorem schreier_lift :
    ∃ f : Subgroup.closure (Set.range pGen) →* lyC ⧸ zGroup,
    Function.Surjective f ∧
      (∀ i, f ⟨pGen i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = ((cC i : lyC) : lyC ⧸ zGroup)) ∧
      (IsSimpleGroup (Subgroup.closure (Set.range pGen)) → (∃ i, cC i ∉ zGroup) →
        Function.Bijective f) :=
  central_Schreier_lift pGen cC closure_cC zGroup zGroup_le_center lyChain chain_hbase
    chain_horbit transversal_mem transversal_base chain_hsift chain_hsiftZ (chain_htermZ cC _)

theorem exists_quotient_equiv :
    ∃ e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11),
    ∀ i : Fin 2, (e (cC i : lyC ⧸ zGroup) : Equiv.Perm (Fin 11)) = pGen i := by
  obtain ⟨f, -, hfp, hbij⟩ := schreier_lift
  have hb := hbij isSimpleGroup_closure_pGen ⟨0, cC_zero_not_mem⟩
  refine ⟨(MulEquiv.ofBijective f hb).symm.trans (MulEquiv.subgroupCongr closure_pGen_eq),
    fun i => ?_⟩
  have : (MulEquiv.ofBijective f hb).symm (cC i : lyC ⧸ zGroup) =
      ⟨pGen i, Subgroup.subset_closure ⟨i, rfl⟩⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact (hfp i).symm
  simp only [MulEquiv.trans_apply, this]
  rfl

@[expose] def lyCoverEquiv :
    lyC ⧸ zGroup ≃* alternatingGroup (Fin 11) :=
  Classical.choose exists_quotient_equiv

theorem lyCoverEquiv_cC (i : Fin 2) :
    (lyCoverEquiv (cC i : lyC ⧸ zGroup) : Equiv.Perm (Fin 11)) = pGen i :=
  Classical.choose_spec exists_quotient_equiv i

@[expose] def imgC :
    lyC →* Equiv.Perm (Fin 11) :=
  (alternatingGroup (Fin 11)).subtype.comp
    (lyCoverEquiv.toMonoidHom.comp (QuotientGroup.mk' zGroup))

theorem imgC_apply (g : lyC) :
    imgC g = (lyCoverEquiv (g : lyC ⧸ zGroup) : Equiv.Perm (Fin 11)) := rfl

theorem imgC_comp_lift :
    imgC.comp (FreeGroup.lift cC) = FreeGroup.lift pGen := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of]
  exact lyCoverEquiv_cC i

theorem imgC_cStar
    {j : ℕ} (hj : j < 12) : imgC ⟨cStar j, cStar_mem j⟩ = pPerm j := by
  have h1 : (⟨cStar j, cStar_mem j⟩ : lyC) = FreeGroup.lift cC (strongF j) :=
    Subtype.ext (lift_cC_strongF j).symm
  rw [h1, ← MonoidHom.comp_apply, imgC_comp_lift, lift_strongF hj]

theorem imgC_zC : imgC zC = 1 := by
  rw [imgC_apply, (QuotientGroup.eq_one_iff (N := zGroup) zC).2 (Subgroup.mem_zpowers zC),
    map_one]
  rfl

theorem imgC_eq_one_iff
    (g : lyC) : imgC g = 1 ↔ g ∈ zGroup := by
  rw [imgC_apply, ← QuotientGroup.eq_one_iff]
  constructor
  · intro h
    apply lyCoverEquiv.injective
    rw [map_one]
    exact Subtype.ext h
  · intro h
    rw [h, map_one]
    rfl

theorem centralizer_double_cover :
    lyz ∈ lyC ∧ (zC : J) = lyz ∧ zC ∈ Subgroup.center lyC ∧ orderOf lyz = 2 ∧
      zGroup = Subgroup.zpowers zC ∧
      ∃ e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11),
        (∀ j < 12, ∀ x : Fin 11,
          (e (QuotientGroup.mk ⟨cStar j, cStar_mem j⟩) : Equiv.Perm (Fin 11)) x = pStar j x) ∧
        Nat.card lyC = 39916800 ∧ Subgroup.center lyC = zGroup := by
  refine ⟨lyz_mem_lyC, rfl, zC_mem_center, orderOf_a, rfl, ?_⟩
  refine ⟨lyCoverEquiv, fun j hj x => ?_, ?_, ?_⟩
  · have := imgC_cStar hj
    rw [imgC_apply] at this
    rw [this, pPerm_apply hj]
  ·
    have hZ : Nat.card zGroup = 2 := by rw [zGroup, Nat.card_zpowers, orderOf_zC]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup zGroup, hZ,
      Nat.card_congr lyCoverEquiv.toEquiv, card_alternating_eleven]
  ·
    apply le_antisymm _ zGroup_le_center
    intro x hx
    have hq : (x : lyC ⧸ zGroup) ∈ Subgroup.center (lyC ⧸ zGroup) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx y]
    have he' : lyCoverEquiv (x : lyC ⧸ zGroup) ∈
        Subgroup.center (alternatingGroup (Fin 11)) := by
      rw [Subgroup.mem_center_iff] at hq ⊢
      intro y
      obtain ⟨y, rfl⟩ := lyCoverEquiv.surjective y
      rw [← map_mul, ← map_mul, hq y]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at he'
    rw [← QuotientGroup.eq_one_iff]
    exact lyCoverEquiv.injective (he'.trans (map_one lyCoverEquiv).symm)

end CFSG.Sporadic.LySchreier
