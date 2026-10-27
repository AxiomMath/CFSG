module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma c23a_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y h
  rw [mkTil_eq_iff] at h
  exact IntMod.val_injective (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h))

private lemma c23a_commElt_le {V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ stabTil (⊥ : Subgroup G) V) : commElt V t ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, hw, rfl⟩
  have htN : t ∈ Subgroup.normalizer (V : Set G) := stabTil_le_normalizer ⊥ V ht
  have h1 : t⁻¹ * w * t ∈ V := (Subgroup.mem_normalizer_iff''.1 htN w).1 hw
  have he : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t) := by group
  rw [he]
  exact V.mul_mem (V.inv_mem hw) h1

private lemma c23a_actStab_inv_mul_val {V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ stabTil (⊥ : Subgroup G) V) (y : IntMod V hV) :
    (actStab (⊥ : Subgroup G) V hV ⟨t, ht⟩⁻¹ y * y⁻¹).val =
      y.val⁻¹ * t⁻¹ * y.val * t := by
  rw [mul_comm (actStab (⊥ : Subgroup G) V hV ⟨t, ht⟩⁻¹ y) y⁻¹]
  rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
  have hcoe : ((⟨t, ht⟩⁻¹ : ↥(stabTil (⊥ : Subgroup G) V)) : G) = t⁻¹ := rfl
  rw [hcoe, inv_inv]
  group

private lemma c23a_tau_inv_mul_inv {V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ stabTil (⊥ : Subgroup G) V) (y : IntMod V hV) :
    ∃ z : IntMod V hV, z.val = y.val⁻¹ * t⁻¹ * y.val * t ∧
      (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩)⁻¹ (mkTil (⊥ : Subgroup G) V hV y) *
        (mkTil (⊥ : Subgroup G) V hV y)⁻¹ = mkTil (⊥ : Subgroup G) V hV z := by
  refine ⟨actStab (⊥ : Subgroup G) V hV ⟨t, ht⟩⁻¹ y * y⁻¹,
    c23a_actStab_inv_mul_val hV ht y, ?_⟩
  rw [← map_inv (actTil (⊥ : Subgroup G) V hV) ⟨t, ht⟩, actTil_mk,
    ← map_inv (mkTil (⊥ : Subgroup G) V hV) y, ← map_mul]

private lemma c23a_zpow_succ_apply {W : Type*} [Group W] (τ : MulAut W) (k : ℤ) (u : W) :
    (τ ^ (k + 1)) u = τ ((τ ^ k) u) := by
  rw [Int.add_comm k 1, zpow_one_add, MulAut.mul_apply]

private lemma c23a_zpow_pred_apply {W : Type*} [Group W] (τ : MulAut W) (k : ℤ) (u : W) :
    (τ ^ (k - 1)) u = τ⁻¹ ((τ ^ k) u) := by
  have h : k - 1 = (-1 : ℤ) + k := by ring
  rw [h, zpow_add, zpow_neg_one, MulAut.mul_apply]

private lemma c23a_mul_eq_inv {W : Type*} [Group W] (τ : MulAut W) (u : W) :
    τ u * u⁻¹ = (τ⁻¹ (τ u) * (τ u)⁻¹)⁻¹ := by
  have h : τ⁻¹ (τ u) = u := by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rw [h, mul_inv_rev, inv_inv]

private lemma c23a_zpow_mul_inv_mem {W : Type*} [CommGroup W] (τ : MulAut W)
    (C' : Subgroup W) (hB1 : ∀ u : W, τ u * u⁻¹ ∈ C')
    (hB2 : ∀ u : W, τ⁻¹ u * u⁻¹ ∈ C') (k : ℤ) (u : W) :
    (τ ^ k) u * u⁻¹ ∈ C' := by
  induction k using Int.induction_on with
  | zero =>
      have h : (τ ^ (0 : ℤ)) u * u⁻¹ = 1 := by simp
      rw [h]
      exact C'.one_mem
  | succ i ih =>
      rw [c23a_zpow_succ_apply]
      rw [show τ ((τ ^ (i : ℤ)) u) * u⁻¹ =
          (τ ((τ ^ (i : ℤ)) u) * ((τ ^ (i : ℤ)) u)⁻¹) *
            (((τ ^ (i : ℤ)) u) * u⁻¹) from by group]
      exact C'.mul_mem (hB1 _) ih
  | pred i ih =>
      rw [c23a_zpow_pred_apply]
      rw [show τ⁻¹ ((τ ^ (-(i : ℤ))) u) * u⁻¹ =
          (τ⁻¹ ((τ ^ (-(i : ℤ))) u) * ((τ ^ (-(i : ℤ))) u)⁻¹) *
            (((τ ^ (-(i : ℤ))) u) * u⁻¹) from by group]
      exact C'.mul_mem (hB2 _) ih

private lemma c23a_commSub_zpowers_le {W : Type*} [CommGroup W] (τ : MulAut W)
    (C' : Subgroup W) (hB1 : ∀ u : W, τ u * u⁻¹ ∈ C')
    (hB2 : ∀ u : W, τ⁻¹ u * u⁻¹ ∈ C') :
    commSub ⊤ (Subgroup.zpowers τ) ≤ C' := by
  refine (Subgroup.closure_le _).2 ?_
  rintro c ⟨x, hx, u, -, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact c23a_zpow_mul_inv_mem τ C' hB1 hB2 k u

theorem c23a_preTil_commSub_zpowers {V : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ stabTil (⊥ : Subgroup G) V) :
    preTil (⊥ : Subgroup G) V hV
        (commSub ⊤ (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩))) =
      commElt V t := by
  have h1 : commElt V t ≤ preTil (⊥ : Subgroup G) V hV
      (commSub ⊤ (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩))) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w, hw, rfl⟩
    have hcV : w⁻¹ * t⁻¹ * w * t ∈ V :=
      c23a_commElt_le hV ht (Subgroup.subset_closure ⟨w, hw, rfl⟩)
    refine (mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV _ hcV).2 ?_
    obtain ⟨z, hzval, hzeq⟩ := c23a_tau_inv_mul_inv hV ht (IntMod.mk hV ⟨w, hw⟩)
    have hz_eq : z = IntMod.mk hV ⟨w⁻¹ * t⁻¹ * w * t, hcV⟩ := by
      apply IntMod.val_injective
      rw [hzval]
      rfl
    rw [← hz_eq, ← hzeq]
    exact Subgroup.subset_closure
      ⟨(actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩)⁻¹,
        Subgroup.inv_mem _ (Subgroup.mem_zpowers _),
        mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨w, hw⟩),
        Subgroup.mem_top _,
        rfl⟩
  have hB2 : ∀ u : Vtil (⊥ : Subgroup G) V hV,
      (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩)⁻¹ u * u⁻¹ ∈
        imgTil (⊥ : Subgroup G) V hV (commElt V t) := by
    intro u
    obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV u
    obtain ⟨z, hzval, hzeq⟩ := c23a_tau_inv_mul_inv hV ht y
    rw [hzeq, mem_imgTil]
    exact ⟨z, Subgroup.subset_closure ⟨y.val, y.val_mem, hzval⟩, rfl⟩
  have hB1 : ∀ u : Vtil (⊥ : Subgroup G) V hV,
      actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ u * u⁻¹ ∈
        imgTil (⊥ : Subgroup G) V hV (commElt V t) := by
    intro u
    have h := hB2 (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ u)
    have he : actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ u * u⁻¹ =
        ((actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩)⁻¹
            (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ u) *
          (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ u)⁻¹)⁻¹ :=
      c23a_mul_eq_inv (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩) u
    rw [he]
    exact (imgTil (⊥ : Subgroup G) V hV (commElt V t)).inv_mem h
  have hC' : commSub ⊤ (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩)) ≤
      imgTil (⊥ : Subgroup G) V hV (commElt V t) :=
    c23a_commSub_zpowers_le _ _ hB1 hB2
  have h2 : preTil (⊥ : Subgroup G) V hV
      (commSub ⊤ (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩))) ≤
      commElt V t := by
    intro g hg
    have hgV : g ∈ V := preTil_le (⊥ : Subgroup G) V hV _ hg
    rw [mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV _ hgV] at hg
    have hgC' : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨g, hgV⟩) ∈
        imgTil (⊥ : Subgroup G) V hV (commElt V t) := hC' hg
    rw [mem_imgTil] at hgC'
    obtain ⟨x, hxmem, hxeq⟩ := hgC'
    have hx_eq : x = IntMod.mk hV ⟨g, hgV⟩ := c23a_mkTil_bot_injective hV hxeq
    rw [hx_eq] at hxmem
    exact hxmem
  exact le_antisymm h2 h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
