module

public import CFSG.Quasithin.EmptyFaithful.S153E55C
public import CFSG.Quasithin.EmptyFaithful.S153E57D
public import CFSG.Quasithin.EmptyFaithful.S153E56In

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E56e

open CFSG.Quasithin.S153E

section General

variable {G : Type} [Group G]

theorem card_conjSubgroup (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A := by
  unfold conjSubgroup
  exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective

theorem conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjSubgroup A g ≤ conjSubgroup B g := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx ⊢
  exact h hx

theorem conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g := by
  ext x
  simp only [mem_conjSubgroup_iff, Subgroup.mem_inf]

theorem conjSubgroup_centralizer (A : Subgroup G) (g : G) :
    conjSubgroup (Subgroup.centralizer (A : Set G)) g =
      Subgroup.centralizer (conjSubgroup A g : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have hw' : g * w * g⁻¹ ∈ A := mem_conjSubgroup_iff.1 hw
    have h1 := h _ hw'
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h1]
      _ = x * w := by group
  · intro h a ha
    have hw : g⁻¹ * a * g ∈ conjSubgroup A g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]
      exact ha
    have h1 := h _ hw
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * a := by group

theorem mem_conj_zpowers {z x : G} (hzz : z * z = 1) (y : G) :
    x ∈ conjSubgroup (Subgroup.zpowers z) y ↔ x = 1 ∨ x = y⁻¹ * z * y := by
  rw [mem_conjSubgroup_iff]
  constructor
  · intro h
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rcases S152O4.eq_one_or_eq_of_mem_zpowers_two hzz h with h1 | h1
    · left
      rw [e, h1]
      group
    · right
      rw [e, h1]
  · rintro (rfl | rfl)
    · simp
    · have e : y * (y⁻¹ * z * y) * y⁻¹ = z := by group
      rw [e]
      exact Subgroup.mem_zpowers z

end General

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Mc_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Mc = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  le_antisymm cx.hF.H_le_centralizer cx.c.hyp.qtfe.centralizer_le_mc

structure Hyps56 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) (y : G) : Prop where
  h113 : StageLemma14113
  c : Chain15355 cx N₁ N₂ g s
  hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)
  iJ : JStruct56 T Mc M V₁ N₁ y
  hrank : mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2)

structure ZGen (T : Subgroup G) (z : G) : Prop where
  eq : quasithinOmegaOneCenter T = Subgroup.zpowers z
  ne : z ≠ 1
  sq : z * z = 1

theorem exists_ZGen (cx : Ctx15350 T Mc M V₁ V₂ t) : ∃ z : G, ZGen T z := by
  obtain ⟨z, -, hz1, hzz, hzeq⟩ := S152O4.exists_eq_zpowers_of_card_two (S153E57.Z_card cx)
  exact ⟨z, hzeq, hz1, hzz⟩

omit [Finite G] in
theorem ZGen.mem {z : G} (hz : ZGen T z) : z ∈ quasithinOmegaOneCenter T := by
  rw [hz.eq]
  exact Subgroup.mem_zpowers z

theorem ZGen.memV (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G} (hz : ZGen T z) : z ∈ VZ T M :=
  cx.c.hyp.Z_le_VZ hz.mem

omit [Finite G] in
theorem ZGen.mem_Z_iff {z x : G} (hz : ZGen T z) :
    x ∈ quasithinOmegaOneCenter T ↔ x = 1 ∨ x = z := by
  rw [hz.eq]
  constructor
  · exact S152O4.eq_one_or_eq_of_mem_zpowers_two hz.sq
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

omit [Finite G] in
theorem ZGen.mem_conj_iff {z x : G} (hz : ZGen T z) (y : G) :
    x ∈ conjSubgroup (quasithinOmegaOneCenter T) y ↔ x = 1 ∨ x = y⁻¹ * z * y := by
  rw [hz.eq]
  exact mem_conj_zpowers hz.sq y

end Setup

section YFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem y_mem_Y (H : Hyps56 cx N₁ N₂ g s y) : y ∈ Y153 Mc M :=
  S153E57.Yi_le_Y N₁ H.hy.1

theorem y_mem_M (H : Hyps56 cx N₁ N₂ g s y) : y ∈ M := Y153_le Mc M (y_mem_Y H)

theorem y_mem_Ni (H : Hyps56 cx N₁ N₂ g s y) : y ∈ Ni153 T Mc M V₁ N₁ :=
  ((oTwoUpper_le _).trans inf_le_right : Yi153 T Mc M V₁ N₁ ≤ Ni153 T Mc M V₁ N₁) H.hy.1

theorem y_mem_YU (H : Hyps56 cx N₁ N₂ g s y) : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
  Subgroup.mem_sup_left (y_mem_Y H)

theorem y_mem_N (H : Hyps56 cx N₁ N₂ g s y) : y ∈ Subgroup.normalizer (VZ T M : Set G) :=
  S153E55.YU_le_normalizer_V cx (y_mem_YU H)

variable (cx) in
abbrev N₁i (N₁ : Subgroup (MulAut ↥(VZ T M))) :
    Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)) := N₁

noncomputable abbrev ybar (H : Hyps56 cx N₁ N₂ g s y) :
    MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) :=
  S153E55.bar cx (y_mem_YU H)

theorem ybar_apply (H : Hyps56 cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    (ybar H w).val = y * w.val * y⁻¹ :=
  S153E55.bar_apply_val cx (y_mem_YU H) w

theorem ybar_mem_N₁ (H : Hyps56 cx N₁ N₂ g s y) : ybar H ∈ N₁ :=
  S153E55.bar_mem_of_mem_Ni cx (y_mem_Ni H) (y_mem_YU H)

theorem N₁_commV_top (c : Chain15355 cx N₁ N₂ g s) : commV (N₁i cx N₁) = ⊤ := by
  have hΩYU := S153E55.autI_YU_eq cx c.h53one
  have hN₁Y : N₁ ≤ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) := hΩYU ▸ le_sup_left
  exact S153E55.commV_eq_top cx hN₁Y c.h53one.comm₁

theorem ybar_pow_three (H : Hyps56 cx N₁ N₂ g s y) : ybar H ^ 3 = 1 := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 H.h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 9 := by
    rw [hYbar]
    exact hS.card_oTwoUpper hT
  have hmem : ybar H ∈ autI hV (Y153 Mc M) := S153E55.bar_mem_autI cx (y_mem_YU H) (y_mem_Y H)
  have h9 : (ybar H) ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥(autI hV (Y153 Mc M))) (x := ⟨ybar H, hmem⟩)
    rw [hY9] at this
    exact congrArg Subtype.val this
  obtain ⟨e⟩ := H.c.h53one.iso₁
  have hN₁ := ybar_mem_N₁ H
  have h9' : (e ⟨ybar H, hN₁⟩) ^ 9 = 1 := by
    rw [← map_pow]
    have : (⟨ybar H, hN₁⟩ : ↥N₁) ^ 9 = 1 := Subtype.ext h9
    rw [this, map_one]
  have h3' : (e ⟨ybar H, hN₁⟩) ^ 3 = 1 := by
    revert h9'
    generalize e ⟨ybar H, hN₁⟩ = σ
    revert σ
    decide +kernel
  have h3 : (⟨ybar H, hN₁⟩ : ↥N₁) ^ 3 = 1 := e.injective (by rw [map_pow, h3', map_one])
  exact congrArg Subtype.val h3

theorem ybar_ne_one (H : Hyps56 cx N₁ N₂ g s y) : ybar H ≠ 1 := by
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

theorem ybar_fixV (H : Hyps56 cx N₁ N₂ g s y) : fixV (Subgroup.zpowers (ybar H)) = ⊥ := by
  obtain ⟨e⟩ := H.c.h53one.iso₁
  exact S153E55.fixV_eq_bot_of_perm (W := IntMod (VZ T M) cx.c.hyp.elemAbelian) IntMod.sq_eq_one e
    (N₁_commV_top H.c) (ybar_mem_N₁ H) (ybar_pow_three H) (ybar_ne_one H)

theorem ybar_cube (H : Hyps56 cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    ybar H (ybar H (ybar H w)) = w := by
  have h := congrArg (fun a : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) => a w)
    (ybar_pow_three H)
  simpa [pow_succ, MulAut.mul_apply] using h

theorem ybar_prod (H : Hyps56 cx N₁ N₂ g s y) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    w * ybar H w * ybar H (ybar H w) = 1 := by
  have hu : ybar H (w * ybar H w * ybar H (ybar H w)) = w * ybar H w * ybar H (ybar H w) := by
    rw [map_mul, map_mul, ybar_cube H]
    ac_rfl
  have hmem : (w * ybar H w * ybar H (ybar H w)) ∈ fixV (Subgroup.zpowers (ybar H)) :=
    mem_fixV_zpowers_iff.2 hu
  rw [ybar_fixV H, Subgroup.mem_bot] at hmem
  exact hmem

theorem y_fpf (H : Hyps56 cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) (h : y * v * y⁻¹ = v) :
    v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (Subgroup.zpowers (ybar H)) := by
    rw [mem_fixV_zpowers_iff]
    refine IntMod.val_injective ?_
    rw [ybar_apply]
    exact h
  rw [ybar_fixV H, Subgroup.mem_bot] at hw
  exact congrArg IntMod.val hw

theorem y_cube (H : Hyps56 cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) :
    y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ = v := by
  have hV := cx.c.hyp.elemAbelian
  have h := congrArg IntMod.val (ybar_cube H (IntMod.mk hV ⟨v, hv⟩))
  rw [ybar_apply, ybar_apply, ybar_apply] at h
  exact h

theorem y_sq_conj (H : Hyps56 cx N₁ N₂ g s y) {v : G} (hv : v ∈ VZ T M) :
    y * (y * v * y⁻¹) * y⁻¹ = y⁻¹ * v * y := by
  have hcube := y_cube H hv
  calc y * (y * v * y⁻¹) * y⁻¹ = y⁻¹ * (y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹) * y := by group
    _ = y⁻¹ * v * y := by rw [hcube]

theorem zp_memV (H : Hyps56 cx N₁ N₂ g s y) {z : G} (hz : ZGen T z) :
    y⁻¹ * z * y ∈ VZ T M := by
  have hyiN : y⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer (VZ T M : Set G)).inv_mem (y_mem_N H)
  have := (Subgroup.mem_normalizer_iff.mp hyiN z).mp (hz.memV cx)
  simpa using this

theorem yz_eq (H : Hyps56 cx N₁ N₂ g s y) {z : G} (hz : ZGen T z) :
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

theorem q_z (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hzV : z ∈ VZ T M) : qV153 cx.c ⟨z, hzV⟩ = 0 := by
  by_contra hq
  have h1 : qV153 cx.c ⟨z, hzV⟩ = 1 := by
    generalize qV153 cx.c ⟨z, hzV⟩ = a at hq ⊢
    revert a
    decide
  obtain ⟨hz12, hz1⟩ := ((qV153_spec cx.c).2.2.2.2 z hzV).1 h1
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, hV₂⟩ := exists_bar_model cx
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hzV⟩
  have hwfix : w ∈ fixV (autI hV T) := (mem_fixV_autI_T_iff cx w).2 hz
  have hτw : τ w = w := hwfix τ hF.τ_T
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg IntMod.val h)
  rcases hz12 with h | h
  · rw [← hV₁] at h
    obtain ⟨w', hw'L, hw'v⟩ := (mem_map_inclMod_iff hV).1 h
    have hww : w' = w := IntMod.val_injective hw'v
    rw [hww] at hw'L
    have hL2 : w ∈ commV L₂ := by
      have := OfourStruct.commV_apply_mem τ L₁ L₂ hF.conj₁ hw'L
      rwa [hτw] at this
    have hmem : w ∈ commV L₁ ⊓ commV L₂ := ⟨hw'L, hL2⟩
    rw [hS.inf, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  · rw [← hV₂] at h
    obtain ⟨w', hw'L, hw'v⟩ := (mem_map_inclMod_iff hV).1 h
    have hww : w' = w := IntMod.val_injective hw'v
    rw [hww] at hw'L
    have hL1 : w ∈ commV L₁ := by
      have := OfourStruct.commV_apply_mem τ L₂ L₁ hF.conj₂ hw'L
      rwa [hτw] at this
    have hmem : w ∈ commV L₁ ⊓ commV L₂ := ⟨hL1, hw'L⟩
    rw [hS.inf, Subgroup.mem_bot] at hmem
    exact hw1 hmem

theorem orth_z_zp (H : Hyps56 cx N₁ N₂ g s y) {z : G} (hz : ZGen T z) :
    Orth153 cx.c z (y⁻¹ * z * y) := by
  have hV := cx.c.hyp.elemAbelian
  refine ⟨hz.memV cx, zp_memV H hz, ?_⟩
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, hz.memV cx⟩
  have hiso : ∀ x : IntMod (VZ T M) hV, qW cx (ybar H x) = qW cx x := by
    have hmem : ybar H ∈ orthogonalGroupOf (qW cx) := by
      rw [← (qW_spec cx).2.2.2]
      exact S153E55.bar_mem_autI cx (y_mem_YU H) (y_mem_M H)
    exact fun x => hmem x
  have hq0 : qW cx w = 0 := q_z cx hz.mem (hz.memV cx)
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

theorem zp_mem_U (H : Hyps56 cx N₁ N₂ g s y) {z : G} (hz : ZGen T z) :
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

theorem zp_ne (H : Hyps56 cx N₁ N₂ g s y) {z : G} (hz : ZGen T z) : y⁻¹ * z * y ≠ z := by
  intro h
  apply hz.ne
  refine y_fpf H (hz.memV cx) ?_
  calc y * z * y⁻¹ = y * (y⁻¹ * z * y) * y⁻¹ := by rw [h]
    _ = z := by group

end YFacts

end S153E56e

end CFSG.Quasithin
