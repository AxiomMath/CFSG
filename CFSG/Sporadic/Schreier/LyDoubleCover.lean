module

public import CFSG.Sporadic.Schreier.LyCover
public import CFSG.Sporadic.Schreier.LyCoverPresM
public import CFSG.Sporadic.Ly.Primitive

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native
open CFSG.Sporadic.SchreierLemmas

theorem lyz_mem_lyC : lyz ∈ lyC := by
  rw [← (car_rels cover_parts.2.2.2.2.2.2).2.2.2]
  exact SetLike.coe_mem _

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

theorem mk_carC_eq {g : lyC} (h : (g : J) = 1 ∨ (g : J) = lyz) :
    (g : lyC ⧸ zGroup) = 1 := by
  rw [QuotientGroup.eq_one_iff, mem_zGroup]
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem exists_quotient_equiv_of_carPresOK (hP : carPresOK csArr = true) :
    ∃ e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11),
    ∀ i : Fin 2, (e (cC i : lyC ⧸ zGroup) : Equiv.Perm (Fin 11)) = pGen i := by
  obtain ⟨h3, h2, hu, -⟩ := car_rels hP
  have hlt : ∀ i j, i < j → ((carC i : lyC ⧸ zGroup) * (carC j : lyC ⧸ zGroup)) ^ 2 = 1 := by
    intro i j h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
    exact mk_carC_eq (h2 i j h)
  have huc : ∀ k : Fin 2,
      FreeGroup.lift (fun i => ((FreeGroup.lift cC (carT i) : lyC) : lyC ⧸ zGroup)) (carU k) =
        (cC k : lyC ⧸ zGroup) := by
    intro k
    have hm := map_list_prod (QuotientGroup.mk' zGroup) ((carGenWords k).map carC)
    rw [List.map_map] at hm
    rw [lift_carU]
    refine Eq.trans hm.symm ?_
    change ((((carGenWords k).map carC).prod : lyC) : lyC ⧸ zGroup) = _
    have hc : (cStar k : J) = (cC k : J) := cSeed_eq_cStar k
    have hp : ((((carGenWords k).map carC).prod : lyC) : J) =
        ((carGenWords k).map fun n => (carC n : J)).prod := by
      rw [← Subgroup.coe_subtype, map_list_prod, List.map_map]
      rfl
    rw [eq_comm, QuotientGroup.eq, mem_zGroup]
    rcases hu k with e | e
    · left
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, inv_mul_eq_one, hp]
      exact (e.trans hc).symm
    · right
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, hp]
      exact e.trans (by rw [hc]; rfl)
  obtain ⟨e, he⟩ := exists_quotient_equiv_of_carmichael cC closure_cC zGroup
    (fun k => FreeGroup.lift CFSG.LocalAnalysis.ComponentInitial.altThreeCycle (carU k)) carT carU
    (fun i => by
      rw [← QuotientGroup.mk_pow]
      exact mk_carC_eq (h3 i))
    (fun i j hij => by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hlt i j h
      · exact CFSG.LocalAnalysis.ComponentInitial.sq_mul_comm_eq_one (hlt j i h))
    (fun _ => rfl) huc cC_zero_not_mem
  exact ⟨e, fun k => by rw [he k, coe_lift_carU]⟩

theorem exists_quotient_equiv :
    ∃ e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11),
    ∀ i : Fin 2, (e (cC i : lyC ⧸ zGroup) : Equiv.Perm (Fin 11)) = pGen i :=
  exists_quotient_equiv_of_carPresOK cover_parts.2.2.2.2.2.2

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
