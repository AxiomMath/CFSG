module

public import CFSG.ClassicalInvolution.Q3.Q3TWLMap
public import CFSG.LieType.Universal.Spin.Twisted.Map
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredSpin
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.AGLEmbeddingD2.SquareSpinMinus
  CFSG.ClassicalInvolution.Q3.Q3TW CFSG.LieType.CurtisTits
  CFSG.Timmesfeld.ClassicalOrders CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {F : Type} [Field F] {b c : F}

abbrev deletionPlanes (r : ℕ) : Finset (Fin (r + 1)) :=
  Finset.univ.erase 0

noncomputable def deletionIsometry (r : ℕ) (b c : F) :
    (quadMinus (r + 1) F b c) →qᵢ (quadMinus (r + 2) F b c) :=
  (minusIsometry F r b c).symm.toIsometry.comp
    (QuadraticMap.Isometry.inr (hypPlane F) (quadMinus (r + 1) F b c))

noncomputable def deletionSpinGroupMap (r : ℕ) (b c : F) :
    spinGroup (quadMinus (r + 1) F b c) →* spinGroup (quadMinus (r + 2) F b c) :=
  (deletionIsometry r b c).spinGroupMap

theorem deletionIsometry_minusVec (r : ℕ) (b c : F) (i : Fin r) (s : Bool) :
    deletionIsometry r b c (minusVec (r + 1) i s) = minusVec (r + 2) i.succ s := by
  change (minusSplit F r).symm ((0, 0), minusVec (r + 1) i s) = minusVec (r + 2) i.succ s
  rw [LinearEquiv.symm_apply_eq]
  refine Prod.ext ?_ ?_
  · cases s <;> simp [minusSplit, minusVec, eVec, fVec, Fin.succ]
  · funext x
    rcases x with j | j | t
    · cases s <;>
        simp [minusSplit, minusVec, eVec, fVec, Fin.succ, Pi.single_apply, Fin.succ_inj,
          Fin.val_inj]
    · cases s <;>
        simp [minusSplit, minusVec, eVec, fVec, Fin.succ, Pi.single_apply, Fin.succ_inj,
          Fin.val_inj]
    · cases s <;> simp [minusSplit, minusVec, eVec, fVec, Fin.succ]

theorem deletionIsometry_planeVec (r : ℕ) (b c : F) (w : Fin 2 → F) :
    deletionIsometry r b c (planeVec (r + 1) w) = planeVec (r + 2) w := by
  change (minusSplit F r).symm ((0, 0), planeVec (r + 1) w) = planeVec (r + 2) w
  rw [LinearEquiv.symm_apply_eq]
  refine Prod.ext ?_ ?_
  · simp [minusSplit, planeVec]
  · funext x
    rcases x with j | j | t <;> simp [minusSplit, planeVec]

theorem deletionIsometry_apply_inl_succ (r : ℕ) (b c : F) (v : Vm (r + 1) F) (j : Fin r) :
    deletionIsometry r b c v (Sum.inl (Fin.succ j)) = v (Sum.inl j) := by
  change (minusSplit F r).symm ((0, 0), v) (Sum.inl (Fin.succ j)) = v (Sum.inl j)
  rfl

theorem deletionIsometry_apply_inr_inl_succ (r : ℕ) (b c : F) (v : Vm (r + 1) F)
    (j : Fin r) :
    deletionIsometry r b c v (Sum.inr (Sum.inl (Fin.succ j))) = v (Sum.inr (Sum.inl j)) := by
  change (minusSplit F r).symm ((0, 0), v) (Sum.inr (Sum.inl (Fin.succ j))) =
    v (Sum.inr (Sum.inl j))
  rfl

theorem deletionIsometry_injective (r : ℕ) (b c : F) :
    Function.Injective (deletionIsometry r b c) := by
  intro v w h
  change (minusSplit F r).symm ((0, 0), v) = (minusSplit F r).symm ((0, 0), w) at h
  exact congrArg Prod.snd ((minusSplit F r).symm.injective h)

theorem deletionIsometry_mem_anchoredSupport (r : ℕ) (b c : F)
    (v : Vm (r + 1) F) :
    deletionIsometry r b c v ∈ anchoredSupport F (r + 2) (deletionPlanes r) := by
  intro a ha
  rcases a with k | k | t
  · revert ha
    refine Fin.cases ?_ (fun j => ?_) k
    · intro ha
      change (minusSplit F r).symm ((0, 0), v) (Sum.inl 0) = 0
      rfl
    · intro ha
      rw [deletionIsometry_apply_inl_succ]
      exfalso
      apply ha
      rw [activeCoords]
      exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _
        (inl_mem_eCoords.2 (by simp [deletionPlanes, Finset.mem_erase, Fin.succ_ne_zero]))))
  · revert ha
    refine Fin.cases ?_ (fun j => ?_) k
    · intro ha
      change (minusSplit F r).symm ((0, 0), v) (Sum.inr (Sum.inl 0)) = 0
      rfl
    · intro ha
      rw [deletionIsometry_apply_inr_inl_succ]
      exfalso
      apply ha
      rw [activeCoords]
      exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _
        (inr_inl_mem_fCoords.2 (by simp [deletionPlanes, Finset.mem_erase,
          Fin.succ_ne_zero]))))
  · exfalso
    apply ha
    exact Finset.mem_coe.2 (Finset.mem_union_right _
      (inr_inr_mem_planeCoords (n := r + 2) t))

theorem finrank_anchoredSupport_deletionPlanes (r : ℕ) (b c : F) :
    Module.finrank F (anchoredSupport F (r + 2) (deletionPlanes r)) = 2 * r + 2 := by
  classical
  let D : Finset (Fin (r + 1)) := deletionPlanes r
  let A : Submodule F (Vm (r + 2) F) := anchoredSupport F (r + 2) D
  have hD : D.card = r := by
    simp [D, deletionPlanes]
  have hdom : Module.finrank F (Vm (r + 1) F) = 2 * r + 2 := by
    change Module.finrank F (Fin r ⊕ Fin r ⊕ Fin 2 → F) = 2 * r + 2
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
    ring
  have hcard : (activeCoords (r + 2) D).card ≤ 2 * r + 2 := by
    rw [activeCoords]
    calc
      ((eCoords (r + 2) D ∪ fCoords (r + 2) D ∪ planeCoords (r + 2)) :
          Finset (Idx (r + 2))).card
          ≤ ((eCoords (r + 2) D ∪ fCoords (r + 2) D).card +
              (planeCoords (r + 2)).card) := Finset.card_union_le _ _
      _ ≤ (((eCoords (r + 2) D).card + (fCoords (r + 2) D).card) +
            (planeCoords (r + 2)).card) := by
            gcongr
            exact Finset.card_union_le _ _
      _ ≤ ((D.card + D.card) + 2) := by
            gcongr
            · exact Finset.card_image_le
            · exact Finset.card_image_le
            · simp only [planeCoords]
              exact Finset.card_le_two
      _ = 2 * r + 2 := by rw [hD]; ring
  have hupper : Module.finrank F A ≤ 2 * r + 2 :=
    (finrank_supp_le (F := F) (T := activeCoords (r + 2) D)).trans hcard
  have hge : 2 * r + 2 ≤ Module.finrank F A := by
    rw [← hdom]
    let f : Vm (r + 1) F →ₗ[F] A :=
      (deletionIsometry r b c).toLinearMap.codRestrict A
        (fun v => deletionIsometry_mem_anchoredSupport r b c v)
    have hf : Function.Injective f := by
      intro v w h
      exact deletionIsometry_injective r b c (congrArg Subtype.val h)
    exact LinearMap.finrank_le_finrank_of_injective hf
  exact le_antisymm hupper hge

@[expose] noncomputable def deletionIsometryEquiv (r : ℕ) (b c : F) :
    (quadMinus (r + 1) F b c).IsometryEquiv
      ((quadMinus (r + 2) F b c).comp
        (anchoredSupport F (r + 2) (deletionPlanes r)).subtype) := by
  classical
  let D : Finset (Fin (r + 1)) := deletionPlanes r
  let A : Submodule F (Vm (r + 2) F) := anchoredSupport F (r + 2) D
  let f : Vm (r + 1) F →ₗ[F] A :=
    (deletionIsometry r b c).toLinearMap.codRestrict A
      (fun v => deletionIsometry_mem_anchoredSupport r b c v)
  have hf : Function.Injective f := by
    intro v w h
    exact deletionIsometry_injective r b c (congrArg Subtype.val h)
  have hrank : Module.finrank F (Vm (r + 1) F) = Module.finrank F A := by
    rw [show A = anchoredSupport F (r + 2) (deletionPlanes r) from rfl,
      finrank_anchoredSupport_deletionPlanes r b c]
    change Module.finrank F (Fin r ⊕ Fin r ⊕ Fin 2 → F) = 2 * r + 2
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum, Fintype.card_fin]
    ring
  let e : Vm (r + 1) F ≃ₗ[F] A := LinearEquiv.ofInjectiveOfFinrankEq f hf hrank
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro v
  change quadMinus (r + 2) F b c (e v : Vm (r + 2) F) = quadMinus (r + 1) F b c v
  have hv : (e v : Vm (r + 2) F) = deletionIsometry r b c v := rfl
  rw [hv, (deletionIsometry r b c).map_app]

@[simp]
theorem deletionIsometryEquiv_apply (r : ℕ) (b c : F)
    (v : Vm (r + 1) F) :
    ((deletionIsometryEquiv r b c).toLinearEquiv v : Vm (r + 2) F) =
      deletionIsometry r b c v :=
  rfl

theorem deletionIsometryEquiv_symm_apply (r : ℕ) (b c : F)
    (a : anchoredSupport F (r + 2) (deletionPlanes r)) :
    deletionIsometry r b c ((deletionIsometryEquiv r b c).symm a) =
      (a : Vm (r + 2) F) := by
  rw [← deletionIsometryEquiv_apply r b c ((deletionIsometryEquiv r b c).symm a)]
  exact congrArg Subtype.val ((deletionIsometryEquiv r b c).apply_symm_apply a)

theorem deletionIsometry_comp_longRoot (r : ℕ) (b c : F) {i j : Fin r} (hij : i ≠ j)
    (s t : Bool) :
    (deletionIsometry r b c).spinGroupMap.comp
        ((minusFrame (r + 1) b c).longRoot hij s t) =
      (minusFrame (r + 2) b c).longRoot ((Fin.succ_injective r).ne hij) s t := by
  refine spinGroupMap_comp_longRoot (deletionIsometry r b c)
    (minusFrame (r + 1) b c).toHypFrame (minusFrame (r + 2) b c).toHypFrame
    hij ((Fin.succ_injective r).ne hij) s t ?_ ?_
  · exact deletionIsometry_minusVec r b c i s
  · exact deletionIsometry_minusVec r b c j t

theorem deletionIsometry_comp_twShortRoot (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin r) (s : Bool) :
    (deletionIsometry r b c).spinGroupMap.comp (twShortRoot (r + 1) hirr i s) =
      twShortRoot (r + 2) hirr (Fin.succ i) s :=
  spinGroupMap_comp_twShortRoot (deletionIsometry r b c) hirr s
    (deletionIsometry_minusVec r b c i s) (deletionIsometry_planeVec r b c)

theorem deletionIsometry_map_rankOne (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin r) :
    (rankOne (minusDatum (r + 1) hirr).rootGroup k).map
        (deletionIsometry r b c).spinGroupMap =
      rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k) := by
  change ((minusRootGroup (r + 1) hirr (Pi.single k 1)) ⊔
      (minusRootGroup (r + 1) hirr (-Pi.single k 1))).map _ =
    minusRootGroup (r + 2) hirr (Pi.single (Fin.succ k) 1) ⊔
      minusRootGroup (r + 2) hirr (-Pi.single (Fin.succ k) 1)
  rw [Subgroup.map_sup]
  by_cases h : k.val + 1 < r
  · have h' : (Fin.succ k).val + 1 < r + 1 := by
      simp only [Fin.val_succ]; omega
    have e1 : (deletionIsometry r b c).spinGroupMap.comp
        ((minusFrame (r + 1) b c).longRoot (succ_ne_of_lt (r + 1) h) true false) =
        (minusFrame (r + 2) b c).longRoot (succ_ne_of_lt (r + 2) h') true false := by
      refine spinGroupMap_comp_longRoot (deletionIsometry r b c)
        (minusFrame (r + 1) b c).toHypFrame (minusFrame (r + 2) b c).toHypFrame
        (succ_ne_of_lt (r + 1) h) (succ_ne_of_lt (r + 2) h') true false ?_ ?_
      · exact deletionIsometry_minusVec r b c k true
      · simpa only [minusFrame_vec, Fin.succ] using
          deletionIsometry_minusVec r b c (⟨k.val + 1, h⟩ : Fin r) false
    have e2 : (deletionIsometry r b c).spinGroupMap.comp
        ((minusFrame (r + 1) b c).longRoot (succ_ne_of_lt (r + 1) h).symm true false) =
        (minusFrame (r + 2) b c).longRoot (succ_ne_of_lt (r + 2) h').symm true false := by
      refine spinGroupMap_comp_longRoot (deletionIsometry r b c)
        (minusFrame (r + 1) b c).toHypFrame (minusFrame (r + 2) b c).toHypFrame
        (succ_ne_of_lt (r + 1) h).symm (succ_ne_of_lt (r + 2) h').symm true false ?_ ?_
      · simpa only [minusFrame_vec, Fin.succ] using
          deletionIsometry_minusVec r b c (⟨k.val + 1, h⟩ : Fin r) true
      · exact deletionIsometry_minusVec r b c k false
    rw [minusRootGroup_single_of_lt (r + 1) hirr h,
      minusRootGroup_neg_single_of_lt (r + 1) hirr h,
      minusRootGroup_single_of_lt (r + 2) hirr h',
      minusRootGroup_neg_single_of_lt (r + 2) hirr h',
      map_range_eq_of_comp_eq _ _ _ e1, map_range_eq_of_comp_eq _ _ _ e2]
  · have h' : ¬ (Fin.succ k).val + 1 < r + 1 := by
      simp only [Fin.val_succ]; omega
    have e1 : (deletionIsometry r b c).spinGroupMap.comp
        (shortPosHom (r + 1) hirr k) =
        shortPosHom (r + 2) hirr (Fin.succ k) := by
      simpa only [twShortRoot_true] using
        deletionIsometry_comp_twShortRoot r b c hirr k true
    have e2 : (deletionIsometry r b c).spinGroupMap.comp
        (shortNegHom (r + 1) hirr k) =
        shortNegHom (r + 2) hirr (Fin.succ k) := by
      simpa only [twShortRoot_false] using
        deletionIsometry_comp_twShortRoot r b c hirr k false
    rw [minusRootGroup_single_of_not_lt (r + 1) hirr h,
      minusRootGroup_neg_single_of_not_lt (r + 1) hirr h,
      minusRootGroup_single_of_not_lt (r + 2) hirr h',
      minusRootGroup_neg_single_of_not_lt (r + 2) hirr h',
      map_range_eq_of_comp_eq _ _ _ e1, map_range_eq_of_comp_eq _ _ _ e2]

theorem deletionSpinGroupMap_range [Finite F] (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) :
    (deletionSpinGroupMap r b c).range =
      ⨆ k : Fin r, rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k) := by
  have hct := minusDatum_isCTGroupDatum (n := r + 1) (K := F) hirr (by omega)
  have hgen := CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
    (D := minusDatum (r + 1) hirr) hct rfl
  exact range_eq_iSup_of_map_eq _ _ _ hgen (deletionIsometry_map_rankOne r b c hirr)

noncomputable def deletionSupportedMap [Finite F] [CharP F 2] (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) :
    spinGroup (quadMinus (r + 1) F b c) →*
      ↥(orthDerived ((quadMinus (r + 2) F b c).comp
        (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)) :=
  (commutatorOrthogonalGroupCongr (deletionIsometryEquiv r b c)).toMonoidHom.comp
    (spinEquivCommutatorQuadMinus (n := r + 1) (by omega) hirr
      (CharTwo.two_eq_zero)).toMonoidHom

theorem deletionSupportedMap_apply [Finite F] [CharP F 2] (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r)
    (x : spinGroup (quadMinus (r + 1) F b c))
    (a : anchoredSupport F (r + 2) (deletionPlanes r)) :
    ((deletionSupportedMap r b c hirr hr x :
        anchoredSupport F (r + 2) (deletionPlanes r) ≃ₗ[F]
          anchoredSupport F (r + 2) (deletionPlanes r)) a : Vm (r + 2) F) =
      deletionIsometry r b c
        (spinAction (quadMinus (r + 1) F b c) x
          ((deletionIsometryEquiv r b c).symm a)) := by
  change ((commutatorOrthogonalGroupCongr (deletionIsometryEquiv r b c)
      (spinEquivCommutatorQuadMinus (n := r + 1) (by omega) hirr
        (CharTwo.two_eq_zero) x) :
      anchoredSupport F (r + 2) (deletionPlanes r) ≃ₗ[F]
        anchoredSupport F (r + 2) (deletionPlanes r)) a : Vm (r + 2) F) = _
  rw [coe_commutatorOrthogonalGroupCongr_apply]
  simp only [LinearEquiv.trans_apply]
  rw [coe_spinEquivCommutatorQuadMinus_apply]
  rw [deletionIsometryEquiv_apply]
  rfl

theorem deletionSupportedSquare [Finite F] [CharP F 2] (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) (hr : 3 ≤ r)
    (hcompl : IsCompl (anchoredSupport F (r + 2) (deletionPlanes r))
      (suppPerp (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)))) :
    (spinAction (quadMinus (r + 2) F b c)).comp (deletionSpinGroupMap r b c) =
      (orthExtend hcompl).comp
        ((orthDerived ((quadMinus (r + 2) F b c).comp
          (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
          (deletionSupportedMap r b c hirr hr)) := by
  classical
  have hgen : ⨆ k : Fin r, rankOne (minusDatum (r + 1) hirr).rootGroup k = ⊤ := by
    have hct := minusDatum_isCTGroupDatum (n := r + 1) (K := F) hirr (by omega)
    exact CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
      (D := minusDatum (r + 1) hirr) hct rfl
  have hclosure : Subgroup.closure
      (⋃ k : Fin r,
        (rankOne (minusDatum (r + 1) hirr).rootGroup k :
          Set (spinGroup (quadMinus (r + 1) F b c)))) = ⊤ := by
    rw [Subgroup.closure_iUnion]
    simpa only [Subgroup.closure_eq] using hgen
  refine MonoidHom.eq_of_eqOn_dense hclosure ?_
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk⟩ := hx
  have hLev : (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
      (spinAction (quadMinus (r + 2) F b c)) ≤
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) := by
    have hI : ∀ j ∈ ({Fin.succ k} : Set (Fin (r + 2 - 1))),
        j ∈ deletionPlanes r ∧ ∀ hj : j.val + 1 < (r + 2) - 1,
          (⟨j.val + 1, hj⟩ : Fin ((r + 2) - 1)) ∈ deletionPlanes r := by
      intro j hj
      rw [Set.mem_singleton_iff] at hj
      subst hj
      refine ⟨?_, ?_⟩
      · simp [deletionPlanes, Finset.mem_erase, Fin.succ_ne_zero]
      · intro hj
        simp [deletionPlanes, Finset.mem_erase]
    calc
      (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
          (spinAction (quadMinus (r + 2) F b c))
          ≤ (leviM (minusDatum (r + 2) hirr)
              ({Fin.succ k} : Set (Fin ((r + 2) - 1)))).map
                (spinAction (quadMinus (r + 2) F b c)) :=
            Subgroup.map_mono (rankOne_le_leviM (Set.mem_singleton _))
      _ ≤ supportedDerived (quadMinus (r + 2) F b c)
            (anchoredSupport F (r + 2) (deletionPlanes r)) :=
            leviM_map_spinAction_le_supportedDerived hirr hcard _ _ hI
  have hx' : deletionSpinGroupMap r b c x ∈
      rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k) := by
    rw [← deletionIsometry_map_rankOne r b c hirr k]
    exact Subgroup.mem_map_of_mem _ hk
  have hLmem : spinAction (quadMinus (r + 2) F b c) (deletionSpinGroupMap r b c x) ∈
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) :=
    hLev (Subgroup.mem_map_of_mem _ hx')
  have hOnA : ∀ a : anchoredSupport F (r + 2) (deletionPlanes r),
      spinAction (quadMinus (r + 2) F b c) (deletionSpinGroupMap r b c x)
          (a : Vm (r + 2) F) =
        (orthExtend hcompl)
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
              (deletionSupportedMap r b c hirr hr x)) (a : Vm (r + 2) F) := by
    intro a
    have heA_symm : deletionIsometry r b c
        ((deletionIsometryEquiv r b c).symm a) = (a : Vm (r + 2) F) :=
      deletionIsometryEquiv_symm_apply r b c a
    have hL : spinAction (quadMinus (r + 2) F b c) (deletionSpinGroupMap r b c x)
        (a : Vm (r + 2) F) =
        deletionIsometry r b c
          (spinAction (quadMinus (r + 1) F b c) x
            ((deletionIsometryEquiv r b c).symm a)) := by
      have hnat := spinAction_spinGroupMap (deletionIsometry r b c) x
        ((deletionIsometryEquiv r b c).symm a)
      rw [heA_symm] at hnat
      exact hnat
    have hR : (orthExtend hcompl)
        ((orthDerived ((quadMinus (r + 2) F b c).comp
          (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
            (deletionSupportedMap r b c hirr hr x)) (a : Vm (r + 2) F) =
        deletionIsometry r b c
          (spinAction (quadMinus (r + 1) F b c) x
            ((deletionIsometryEquiv r b c).symm a)) := by
      have hR1 : (orthExtend hcompl)
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
              (deletionSupportedMap r b c hirr hr x)) (a : Vm (r + 2) F) =
          ((deletionSupportedMap r b c hirr hr x :
            anchoredSupport F (r + 2) (deletionPlanes r) ≃ₗ[F]
              anchoredSupport F (r + 2) (deletionPlanes r)) a : Vm (r + 2) F) := by
        rw [show (a : Vm (r + 2) F) =
            ((a : anchoredSupport F (r + 2) (deletionPlanes r)) : Vm (r + 2) F) +
              ((0 : suppPerp (quadMinus (r + 2) F b c)
                (anchoredSupport F (r + 2) (deletionPlanes r))) : Vm (r + 2) F) by simp]
        rw [orthExtend_apply hcompl ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
              (deletionSupportedMap r b c hirr hr x)) a
          (0 : suppPerp (quadMinus (r + 2) F b c)
            (anchoredSupport F (r + 2) (deletionPlanes r)))]
        simp
      exact hR1.trans (deletionSupportedMap_apply r b c hirr hr x a)
    exact hL.trans hR.symm
  have hOnPerp : ∀ w ∈ suppPerp (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (deletionPlanes r)),
      spinAction (quadMinus (r + 2) F b c) (deletionSpinGroupMap r b c x) w =
        (orthExtend hcompl)
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
              (deletionSupportedMap r b c hirr hr x)) w := by
    intro w hw
    have hLfix : spinAction (quadMinus (r + 2) F b c) (deletionSpinGroupMap r b c x) w = w :=
      (mem_supportedDerived.mp hLmem).1 w hw
    have hRfix : (orthExtend hcompl)
        ((orthDerived ((quadMinus (r + 2) F b c).comp
          (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
            (deletionSupportedMap r b c hirr hr x)) w = w := by
      rw [show w = ((0 : anchoredSupport F (r + 2) (deletionPlanes r)) : Vm (r + 2) F) +
        (w : Vm (r + 2) F) by simp]
      rw [orthExtend_apply hcompl ((orthDerived ((quadMinus (r + 2) F b c).comp
          (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype
            (deletionSupportedMap r b c hirr hr x))
        (0 : anchoredSupport F (r + 2) (deletionPlanes r)) ⟨w, hw⟩]
      simp
    rw [hLfix, hRfix]
  have hOnA' : ∀ a ∈ anchoredSupport F (r + 2) (deletionPlanes r),
      ((spinAction (quadMinus (r + 2) F b c)).comp (deletionSpinGroupMap r b c)) x a =
        ((orthExtend hcompl).comp
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
              (deletionSupportedMap r b c hirr hr))) x a :=
    fun a ha => hOnA ⟨a, ha⟩
  have hOnPerp' : ∀ w ∈ suppPerp (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (deletionPlanes r)),
      ((spinAction (quadMinus (r + 2) F b c)).comp (deletionSpinGroupMap r b c)) x w =
        ((orthExtend hcompl).comp
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
              (deletionSupportedMap r b c hirr hr))) x w :=
    fun w hw => hOnPerp w hw
  ext v
  obtain ⟨a, ha, w, hw, hvw⟩ := suppExists_add_of_isCompl hcompl v
  rw [← hvw, map_add, map_add, hOnA' a ha, hOnPerp' w hw]

theorem supportedDerived_anchoredSupport_eq_iSup_rankOne_map_spinAction
    [Finite F] [CharP F 2] (r : ℕ) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) (hr : 3 ≤ r) :
    supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) =
      ⨆ k : Fin r,
        (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
          (spinAction (quadMinus (r + 2) F b c)) := by
  classical
  have hreg : PolarNondegOn (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (deletionPlanes r)) :=
    polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c)
      (S := deletionPlanes r) hirr
  have hcompl : IsCompl (anchoredSupport F (r + 2) (deletionPlanes r))
      (suppPerp (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r))) :=
    isCompl_suppPerp hreg
  have hsquare := deletionSupportedSquare r b c hirr hcard hr hcompl
  have hrangeL : ((spinAction (quadMinus (r + 2) F b c)).comp
        (deletionSpinGroupMap r b c)).range =
      ⨆ k : Fin r,
        (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
          (spinAction (quadMinus (r + 2) F b c)) := by
    rw [MonoidHom.range_comp, deletionSpinGroupMap_range r b c hirr hr]
    exact Subgroup.map_iSup _ _
  have hrangeR : ((orthExtend hcompl).comp
      ((orthDerived ((quadMinus (r + 2) F b c).comp
        (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
          (deletionSupportedMap r b c hirr hr))).range =
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) := by
    have hρrange : (deletionSupportedMap r b c hirr hr).range = ⊤ := by
      apply MonoidHom.range_eq_top.mpr
      exact (commutatorOrthogonalGroupCongr (deletionIsometryEquiv r b c)).surjective.comp
        (spinEquivCommutatorQuadMinus (n := r + 1) (by omega) hirr
          (CharTwo.two_eq_zero)).surjective
    have hsub : ((orthDerived ((quadMinus (r + 2) F b c).comp
        (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
          (deletionSupportedMap r b c hirr hr)).range =
        orthDerived ((quadMinus (r + 2) F b c).comp
          (anchoredSupport F (r + 2) (deletionPlanes r)).subtype) := by
      rw [MonoidHom.range_comp, hρrange, Subgroup.map_top, Subgroup.range_subtype]
    calc
      ((orthExtend hcompl).comp
          ((orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
              (deletionSupportedMap r b c hirr hr))).range
          = (((orthDerived ((quadMinus (r + 2) F b c).comp
              (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).subtype.comp
                (deletionSupportedMap r b c hirr hr)).range).map (orthExtend hcompl) :=
            MonoidHom.range_comp _ _
      _ = (orthDerived ((quadMinus (r + 2) F b c).comp
            (anchoredSupport F (r + 2) (deletionPlanes r)).subtype)).map
              (orthExtend hcompl) := by rw [hsub]
      _ = supportedDerived (quadMinus (r + 2) F b c)
            (anchoredSupport F (r + 2) (deletionPlanes r)) :=
            map_orthDerived_orthExtend_eq_supportedDerived hcompl
  have hrange : ((spinAction (quadMinus (r + 2) F b c)).comp
        (deletionSpinGroupMap r b c)).range =
      supportedDerived (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) := by
    rw [hsquare, hrangeR]
  rw [← hrangeL, hrange]

end CFSG.RankThree.PartOne.KCOrthogonal
