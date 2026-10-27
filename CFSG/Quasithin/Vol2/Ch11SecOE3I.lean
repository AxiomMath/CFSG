module

public import CFSG.Quasithin.Vol2.Ch11SecOE3H

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r) [IsMulCommutative ↥(fsuV T I)]
include h

theorem isXSectionIso_map {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I)))) :
    IsXSectionIso K (reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G))
      (((I.subgroupOf (fsuV T I)).map b.toMonoidHom).map (fsuV T I).subtype ⊔
        reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G))
      (I ⊔ reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G)) := by
  set C := reducedAggregate (K ⊔ T) ⊓ Subgroup.centralizer (K : Set G) with hCdef
  set B := ((I.subgroupOf (fsuV T I)).map b.toMonoidHom).map (fsuV T I).subtype with hBdef
  have hIV : I ≤ fsuV T I := I_le_V T I
  have hVR : fsuV T I ≤ reducedAggregate (K ⊔ T) := h.le_reducedAggregate
  have hRc := (Vol2.Ch11.SecA.reducedAggregate_props (K ⊔ T)).2.1
  have hBR : B ≤ reducedAggregate (K ⊔ T) := (Subgroup.map_subtype_le _).trans hVR
  have hnorm : ∀ {J : Subgroup G}, J ≤ reducedAggregate (K ⊔ T) → (C.subgroupOf J).Normal :=
    fun hJ => ⟨fun n hn g => by
      have e : g * n * g⁻¹ = n := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hRc _ (hJ g.2) _ (hJ n.2), mul_inv_cancel_right])
      rw [e]
      exact hn⟩
  have hnJ : (C.subgroupOf (B ⊔ C)).Normal := hnorm (sup_le hBR inf_le_left)
  have hnI : (C.subgroupOf (I ⊔ C)).Normal := hnorm (sup_le (hIV.trans hVR) inf_le_left)
  have hcent : ∀ {X : Subgroup G}, X ≤ reducedAggregate (K ⊔ T) →
      X ≤ Subgroup.normalizer (C : Set G) := fun hX x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun c hc =>
      hRc _ hc.1 _ (hX hx))
  have hbJ : ∀ i : ↥I, ((b ⟨i, hIV i.2⟩ : ↥(fsuV T I)) : G) ∈ B ⊔ C := fun i =>
    Subgroup.mem_sup_left ⟨b ⟨i, hIV i.2⟩, ⟨⟨i, hIV i.2⟩, i.2, rfl⟩, rfl⟩
  let β : ↥I →* ↥(B ⊔ C) :=
    ((fsuV T I).subtype.comp (b.toMonoidHom.comp (Subgroup.inclusion hIV))).codRestrict _ hbJ
  have hβ : ∀ x : ↥I, ((β x : ↥(B ⊔ C)) : G) = ((b ⟨x, hIV x.2⟩ : ↥(fsuV T I)) : G) :=
    fun _ => rfl
  let θ : ↥I →* ↥(B ⊔ C) ⧸ C.subgroupOf (B ⊔ C) := (QuotientGroup.mk' _).comp β
  let θ' : ↥I →* ↥(I ⊔ C) ⧸ C.subgroupOf (I ⊔ C) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
  have hθ : ∀ x, θ x = ((β x : ↥(B ⊔ C)) : ↥(B ⊔ C) ⧸ C.subgroupOf (B ⊔ C)) := fun _ => rfl
  have hθ' : ∀ x : ↥I, θ' x = ((⟨x, Subgroup.mem_sup_left x.2⟩ : ↥(I ⊔ C)) :
      ↥(I ⊔ C) ⧸ C.subgroupOf (I ⊔ C)) := fun _ => rfl
  have hθs : Function.Surjective θ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      have hj : (j : G) ∈ ((B ⊔ C : Subgroup G) : Set G) := j.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B C (hcent hBR)] at hj
      obtain ⟨_, ⟨y, ⟨v, hv, rfl⟩, rfl⟩, c, hc, hjc⟩ := hj
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom] at hjc
      refine ⟨⟨v, hv⟩, ?_⟩
      rw [hθ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show ((b v : ↥(fsuV T I)) : G)⁻¹ * (j : G) ∈ C
      rw [← hjc, inv_mul_cancel_left]
      exact hc
  have hθ's : Function.Surjective θ' := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      have hj : (j : G) ∈ ((I ⊔ C : Subgroup G) : Set G) := j.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right I C (hcent (hIV.trans hVR))] at hj
      obtain ⟨i, hi, c, hc, hic⟩ := hj
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [hθ', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (i : G)⁻¹ * (j : G) ∈ C
      rw [← hic, inv_mul_cancel_left]
      exact hc
  have hker : θ.ker = θ'.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθ, hθ', QuotientGroup.eq_one_iff,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hβ,
      h.coe_mem_cent_iff, apply_mem_fixV_iff hb, ← h.coe_mem_cent_iff]
  let e : ↥(B ⊔ C) ⧸ C.subgroupOf (B ⊔ C) ≃* ↥(I ⊔ C) ⧸ C.subgroupOf (I ⊔ C) :=
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ' hθ's))
  have he : ∀ x : ↥I, e (θ x) = θ' x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm (θ x) =
        (x : ↥I ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [e, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine ⟨hnJ, hnI, e, ?_⟩
  intro k hk j y hj hy hjy
  obtain ⟨x, hx⟩ := hθs (j : ↥(B ⊔ C) ⧸ C.subgroupOf (B ⊔ C))
  have hxk : k * (x : G) * k⁻¹ ∈ I :=
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_I hk) x).mp x.2
  have h1 : θ ⟨k * x * k⁻¹, hxk⟩ =
      ((⟨k * j * k⁻¹, hj⟩ : ↥(B ⊔ C)) : ↥(B ⊔ C) ⧸ C.subgroupOf (B ⊔ C)) := by
    rw [hθ] at hx ⊢
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx ⊢
    have e1 : ((β ⟨k * x * k⁻¹, hxk⟩ : ↥(B ⊔ C)) : G) = k * ((β x : ↥(B ⊔ C)) : G) * k⁻¹ :=
      h.coe_apply_conj hb hk ⟨x, hIV x.2⟩ (hIV hxk)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hx ⊢
    rw [e1]
    have := conj_mem_cent hk hx
    convert this using 1
    group
  have h2 : θ' ⟨k * x * k⁻¹, hxk⟩ =
      ((⟨k * y * k⁻¹, hy⟩ : ↥(I ⊔ C)) : ↥(I ⊔ C) ⧸ C.subgroupOf (I ⊔ C)) := by
    have hy' : θ' x = (y : ↥(I ⊔ C) ⧸ C.subgroupOf (I ⊔ C)) := by
      rw [← he, hx]
      exact hjy
    rw [hθ'] at hy' ⊢
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hy' ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hy' ⊢
    have := conj_mem_cent hk hy'
    convert this using 1
    group
  rw [← h1, he, h2]

theorem map_mem_I {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I))))
    {v : ↥(fsuV T I)} (hv : v ∈ I.subgroupOf (fsuV T I)) : b v ∈ I.subgroupOf (fsuV T I) := by
  have hJ := h.homog _ le_sup_right (sup_le_sup_right (Subgroup.map_subtype_le _) _)
    (h.le_normalizer_sup hb) (h.isXSectionIso_map hb)
  have hcs : commSub (I.subgroupOf (fsuV T I)) (autOn K (fsuV T I)) =
      I.subgroupOf (fsuV T I) := by
    rw [commSub_autOn_eq h.le_normalizer_V (I_le_V T I), h.commutator_I]
  have key : commSub (I.subgroupOf (fsuV T I)) (autOn K (fsuV T I)) ≤
      (I.subgroupOf (fsuV T I)).comap b.toMonoidHom := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Ch10.SecA.mem_autOn_iff'.mp hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    have hkw : k * (w : G) * k⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp hkN w).mp w.2
    have e : conjAct (fsuV T I) ⟨k, hkN⟩ w = ⟨k * w * k⁻¹, hkw⟩ :=
      Subtype.ext (Ch10.SecA.coe_conjAct_apply' _ w)
    rw [e, h.coe_apply_conj hb hk w hkw]
    exact h.comm_mem_of_mem_sup (hJ (Subgroup.mem_sup_left ⟨b w, ⟨w, hw, rfl⟩, rfl⟩)) hk
  rw [← hcs] at hv
  exact key hv

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
