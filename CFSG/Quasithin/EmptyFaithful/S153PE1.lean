module

public import CFSG.Quasithin.EmptyFaithful.S153E56E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153P

namespace PE

open CFSG.Quasithin.S153E

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure HypsA (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y : G) : Prop where
  h113 : StageLemma14113
  c : Chain15355 cx N₁ N₂ g s
  hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)

end Setup

section YFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

omit [Finite G] in
theorem Yi_mem_Y (N₁ : Subgroup (MulAut ↥(VZ T M))) {x : G} (hx : x ∈ Yi153 T Mc M V₁ N₁) :
    x ∈ Y153 Mc M :=
  S153E57.Yi_le_Y N₁ hx

omit [Finite G] in
theorem Yi_mem_Ni {x : G} (hx : x ∈ Yi153 T Mc M V₁ N₁) : x ∈ Ni153 T Mc M V₁ N₁ :=
  ((oTwoUpper_le _).trans inf_le_right : Yi153 T Mc M V₁ N₁ ≤ Ni153 T Mc M V₁ N₁) hx

omit [Finite G] in
theorem Yi_mem_YU (N₁ : Subgroup (MulAut ↥(VZ T M))) {x : G} (hx : x ∈ Yi153 T Mc M V₁ N₁) :
    x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
  Subgroup.mem_sup_left (Yi_mem_Y N₁ hx)

theorem y_mem_Y (H : HypsA cx N₁ N₂ g s y) : y ∈ Y153 Mc M :=
  Yi_mem_Y N₁ H.hy.1

theorem y_mem_M (H : HypsA cx N₁ N₂ g s y) : y ∈ M := Y153_le Mc M (y_mem_Y H)

theorem y_mem_Ni (H : HypsA cx N₁ N₂ g s y) : y ∈ Ni153 T Mc M V₁ N₁ :=
  Yi_mem_Ni H.hy.1

theorem y_mem_YU (H : HypsA cx N₁ N₂ g s y) : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
  Yi_mem_YU N₁ H.hy.1

theorem y_mem_N (H : HypsA cx N₁ N₂ g s y) : y ∈ Subgroup.normalizer (VZ T M : Set G) :=
  S153E55.YU_le_normalizer_V cx (y_mem_YU H)

noncomputable abbrev ybar (H : HypsA cx N₁ N₂ g s y) :
    MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) :=
  S153E55.bar cx (y_mem_YU H)

theorem ybar_apply (H : HypsA cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    (ybar H w).val = y * w.val * y⁻¹ :=
  S153E55.bar_apply_val cx (y_mem_YU H) w

theorem ybar_mem_N₁ (H : HypsA cx N₁ N₂ g s y) : ybar H ∈ N₁ :=
  S153E55.bar_mem_of_mem_Ni cx (y_mem_Ni H) (y_mem_YU H)

theorem bar_pow_three (H : HypsA cx N₁ N₂ g s y) {x : G} (hx : x ∈ Yi153 T Mc M V₁ N₁) :
    S153E55.bar cx (Yi_mem_YU N₁ hx) ^ 3 = 1 := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 H.h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 9 := by
    rw [hYbar]
    exact hS.card_oTwoUpper hT
  have hmem : S153E55.bar cx (Yi_mem_YU N₁ hx) ∈ autI hV (Y153 Mc M) :=
    S153E55.bar_mem_autI cx (Yi_mem_YU N₁ hx) (Yi_mem_Y N₁ hx)
  have h9 : (S153E55.bar cx (Yi_mem_YU N₁ hx)) ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥(autI hV (Y153 Mc M)))
      (x := ⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hmem⟩)
    rw [hY9] at this
    exact congrArg Subtype.val this
  obtain ⟨e⟩ := H.c.h53one.iso₁
  have hN₁ : S153E55.bar cx (Yi_mem_YU N₁ hx) ∈ N₁ :=
    S153E55.bar_mem_of_mem_Ni cx (Yi_mem_Ni hx) (Yi_mem_YU N₁ hx)
  have h9' : (e ⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hN₁⟩) ^ 9 = 1 := by
    rw [← map_pow]
    have : (⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hN₁⟩ : ↥N₁) ^ 9 = 1 := Subtype.ext h9
    rw [this, map_one]
  have h3' : (e ⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hN₁⟩) ^ 3 = 1 := by
    revert h9'
    generalize e ⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hN₁⟩ = σ
    revert σ
    decide +kernel
  have h3 : (⟨S153E55.bar cx (Yi_mem_YU N₁ hx), hN₁⟩ : ↥N₁) ^ 3 = 1 :=
    e.injective (by rw [map_pow, h3', map_one])
  exact congrArg Subtype.val h3

theorem ybar_pow_three (H : HypsA cx N₁ N₂ g s y) : ybar H ^ 3 = 1 :=
  bar_pow_three H H.hy.1

theorem ybar_ne_one (H : HypsA cx N₁ N₂ g s y) : ybar H ≠ 1 := by
  intro h1
  have hC : y ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (convI_eq_one_iff cx.c.hyp.elemAbelian ⟨y, y_mem_N H⟩).1 h1
  have hyO : y ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [cx.r49.case_one.1]
    exact ⟨y_mem_Y H, hC⟩
  have hle : Yi153 T Mc M V₁ N₁ ⊓ pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 (Yi153 T Mc M V₁ N₁) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, le_normalizer_pCoreOf 2 _ (S153E57.Yi_le_Y N₁ ha)⟩
  exact H.hy.2 (hle ⟨H.hy.1, hyO⟩)

theorem ybar_fixV (H : HypsA cx N₁ N₂ g s y) : fixV (Subgroup.zpowers (ybar H)) = ⊥ := by
  obtain ⟨e⟩ := H.c.h53one.iso₁
  exact S153E55.fixV_eq_bot_of_perm (W := IntMod (VZ T M) cx.c.hyp.elemAbelian) IntMod.sq_eq_one e
    (S153E56e.N₁_commV_top H.c) (ybar_mem_N₁ H) (ybar_pow_three H) (ybar_ne_one H)

theorem ybar_cube (H : HypsA cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    ybar H (ybar H (ybar H w)) = w := by
  have h := congrArg (fun a : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) => a w)
    (ybar_pow_three H)
  simpa [pow_succ, MulAut.mul_apply] using h

theorem ybar_prod (H : HypsA cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    w * ybar H w * ybar H (ybar H w) = 1 := by
  have hu : ybar H (w * ybar H w * ybar H (ybar H w)) = w * ybar H w * ybar H (ybar H w) := by
    rw [map_mul, map_mul, ybar_cube H]
    ac_rfl
  have hmem : (w * ybar H w * ybar H (ybar H w)) ∈ fixV (Subgroup.zpowers (ybar H)) :=
    mem_fixV_zpowers_iff.2 hu
  rw [ybar_fixV H, Subgroup.mem_bot] at hmem
  exact hmem

theorem y_fpf (H : HypsA cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) (h : y * v * y⁻¹ = v) :
    v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (Subgroup.zpowers (ybar H)) := by
    rw [mem_fixV_zpowers_iff]
    refine IntMod.val_injective ?_
    rw [ybar_apply]
    exact h
  rw [ybar_fixV H, Subgroup.mem_bot] at hw
  exact congrArg IntMod.val hw

theorem y_cube (H : HypsA cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) :
    y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ = v := by
  have hV := cx.c.hyp.elemAbelian
  have h := congrArg IntMod.val (ybar_cube H (IntMod.mk hV ⟨v, hv⟩))
  rw [ybar_apply, ybar_apply, ybar_apply] at h
  exact h

theorem y_sq_conj (H : HypsA cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) :
    y * (y * v * y⁻¹) * y⁻¹ = y⁻¹ * v * y := by
  have hcube := y_cube H hv
  calc y * (y * v * y⁻¹) * y⁻¹ = y⁻¹ * (y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹) * y := by group
    _ = y⁻¹ * v * y := by rw [hcube]

theorem zp_memV (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    y⁻¹ * z * y ∈ VZ T M := by
  have hyiN : y⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer (VZ T M : Set G)).inv_mem (y_mem_N H)
  have := (Subgroup.mem_normalizer_iff.mp hyiN z).mp (hz.memV cx)
  simpa using this

theorem yz_eq (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    y * z * y⁻¹ = z * (y⁻¹ * z * y) := by
  have hV := cx.c.hyp.elemAbelian
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hz.memV cx⟩
  have hprod := ybar_prod H w
  have h2 : ∀ q : IntMod (VZ T M) hV, q * q = 1 := fun q => by
    rw [← pow_two]
    exact IntMod.sq_eq_one q
  have key : ybar H w = w * ybar H (ybar H w) := by
    calc ybar H w = ybar H w * (w * w) * (ybar H (ybar H w) * ybar H (ybar H w)) := by
          rw [h2, h2]
          simp
      _ = (w * ybar H w * ybar H (ybar H w)) * (w * ybar H (ybar H w)) := by ac_rfl
      _ = w * ybar H (ybar H w) := by rw [hprod, one_mul]
  have e1 := congrArg IntMod.val key
  rw [IntMod.val_mul, ybar_apply, ybar_apply, ybar_apply] at e1
  have e2 := y_sq_conj H (hz.memV cx)
  have e3 : (w.val : G) = z := rfl
  rw [e3] at e1
  rw [e1, e2]

theorem orth_z_zp (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    Orth153 cx.c z (y⁻¹ * z * y) := by
  have hV := cx.c.hyp.elemAbelian
  refine ⟨hz.memV cx, zp_memV H hz, ?_⟩
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hz.memV cx⟩
  have hiso : ∀ x : IntMod (VZ T M) hV, qW cx (ybar H x) = qW cx x := by
    have hmem : ybar H ∈ orthogonalGroupOf (qW cx) := by
      rw [← (qW_spec cx).2.2.2]
      exact S153E55.bar_mem_autI cx (y_mem_YU H) (y_mem_M H)
    exact fun x => hmem x
  have hq0 : qW cx w = 0 := S153E56e.q_z cx hz.mem (hz.memV cx)
  have hbw : ybar H (ybar H w) = IntMod.mk hV ⟨y⁻¹ * z * y, zp_memV H hz⟩ := by
    refine IntMod.val_injective ?_
    rw [ybar_apply, ybar_apply]
    exact y_sq_conj H (hz.memV cx)
  have hkey : ybar H w = w * ybar H (ybar H w) := by
    refine IntMod.val_injective ?_
    rw [IntMod.val_mul, ybar_apply, ybar_apply, ybar_apply]
    have e3 : (w.val : G) = z := rfl
    rw [e3, y_sq_conj H (hz.memV cx)]
    exact yz_eq H hz
  show quadPolar (qW cx) w (IntMod.mk hV ⟨y⁻¹ * z * y, zp_memV H hz⟩) = 0
  rw [← hbw]
  unfold quadPolar
  rw [← hkey, hiso w, hiso (ybar H w), hiso w, hq0]
  decide

theorem zp_mem_U (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    y⁻¹ * z * y ∈ UH153 T M V₁ Mc := by
  obtain ⟨P, hP, hVQ, hVU, hUV⟩ := H.c.h53two.perp
  have hzpP : y⁻¹ * z * y ∈ P := by
    refine (hP _).2 ⟨zp_memV H hz, fun a ha => ?_⟩
    rcases hz.mem_Z_iff.1 ha with rfl | rfl
    · have h1 : quadPolar (qW cx) (1 : IntMod (VZ T M) cx.c.hyp.elemAbelian)
          (IntMod.mk cx.c.hyp.elemAbelian ⟨y⁻¹ * z * y, zp_memV H hz⟩) = 0 :=
        quadPolar_one_left (qW_spec cx).1 _
      exact ⟨Subgroup.one_mem _, zp_memV H hz, h1⟩
    · exact orth_z_zp H hz
  rw [← hVU] at hzpP
  exact hzpP.2

theorem zp_ne (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) : y⁻¹ * z * y ≠ z := by
  intro h
  apply hz.ne
  refine y_fpf H (hz.memV cx) ?_
  calc y * z * y⁻¹ = y * (y⁻¹ * z * y) * y⁻¹ := by rw [h]
    _ = z := by group

end YFacts

end PE

end S153P

end CFSG.Quasithin
