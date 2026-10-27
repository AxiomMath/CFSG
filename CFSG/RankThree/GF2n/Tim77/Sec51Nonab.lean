module

public import CFSG.RankThree.GF2n.Tim77.Sec51Basic
public import CFSG.RankThree.GF2n.Tim77.Sec32b
public import CFSG.RankThree.GF2n.Tim77.Sec43Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem Prop24Setup.tr_of_mem_Lb [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {b : G} (hb : b ∈ Lb) : Sec51Tr A L b where
  mem_normalizer := (S.mem_Lb.mp hb).2
  comm_zero := fun y hy => (S.comm_L_Lb hy hb).symm
  commutator_mem := fun x hx => by
    have h1 := L.inv_mem (S.commutator_mem_L hx hb)
    have e : b * x * b⁻¹ * x⁻¹ = (x * b * x⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact h1

theorem Prop24Setup.eq_one_of_mem_Ab_of_centralizes [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {w : G} (hw : w ∈ Ab) (hc : ∀ x ∈ A, w * x = x * w) :
    w = 1 := by
  obtain ⟨t, htA, htL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  have hwLb : w ∈ Lb := S.mem_Lb_of_commute hw htA ht1 (hc t htA)
  have hwL : w ∈ L := S.mem_L_of_commute_M htA htL (S.Lb_le_M hwLb) (hc t htA).symm
  have : w ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le hwL, hw⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at this
  exact this

structure Sec51Bad (A Abar S₀ B S : Subgroup G) (h a b : G) : Prop where
  ctx : Sec3Ctx A Abar S₀ B
  hq : Section3.q A Abar = 2
  hS : IsPGroup 2 S
  hSN : S ≤ normalizer (Section3.A0 A Abar : Set G)
  hAb0S : Section3.Abar0 A Abar ≤ S
  hh : h ∈ S
  ha : a ∈ conjSubgroup h (Section3.Abar0 A Abar)
  hb : b ∈ Section3.Abar0 A Abar
  ha2 : a * a = 1
  hb2 : b * b = 1
  hord : orderOf (a * b) = 4

namespace Sec51Bad

variable [Finite G] {A Abar S₀ B S : Subgroup G} {h a b : G}

theorem normalizer_A0_le (H : Sec51Bad A Abar S₀ B S h a b) :
    normalizer (Section3.A0 A Abar : Set G) ≤ normalizer (A : Set G) :=
  sec51_normalizer_le H.ctx.hyp.ti H.ctx.setup.L_le H.ctx.a0_ne_bot

theorem h_mem_normalizer_A (H : Sec51Bad A Abar S₀ B S h a b) : h ∈ normalizer (A : Set G) :=
  H.normalizer_A0_le (H.hSN H.hh)

theorem tr_b (H : Sec51Bad A Abar S₀ B S h a b) : Sec51Tr A (Section3.A0 A Abar) b :=
  H.ctx.setup.tr_of_mem_Lb H.hb

theorem tr_a (H : Sec51Bad A Abar S₀ B S h a b) : Sec51Tr A (Section3.A0 A Abar) a := by
  obtain ⟨b', hb', rfl⟩ := (mem_conjSubgroup_exists_t77 h _ a).1 H.ha
  exact (H.ctx.setup.tr_of_mem_Lb hb').conj H.h_mem_normalizer_A (H.hSN H.hh)

theorem v_ctx (H : Sec51Bad A Abar S₀ B S h a b) :
    Sec3Ctx A (conjSubgroup h Abar) (conjSubgroup h S₀) (conjSubgroup h B) := by
  have := H.ctx.conj h
  rwa [conjSubgroup_eq_self_iff.mpr H.h_mem_normalizer_A] at this

theorem a_mem_V (H : Sec51Bad A Abar S₀ B S h a b) : a ∈ conjSubgroup h Abar :=
  (conjSubgroup_le_conj_iff h).2 H.ctx.setup.Lb_le H.ha

theorem a_ne_one (H : Sec51Bad A Abar S₀ B S h a b) : a ≠ 1 := by
  intro h1
  have h4 := H.hord
  rw [h1, one_mul] at h4
  have h2 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact H.hb2)
  rw [h4] at h2
  omega

theorem b_ne_one (H : Sec51Bad A Abar S₀ B S h a b) : b ≠ 1 := by
  intro h1
  have h4 := H.hord
  rw [h1, mul_one] at h4
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact H.ha2)
  rw [h4] at h2
  omega

theorem w_centralizes (H : Sec51Bad A Abar S₀ B S h a b) {x : G} (hx : x ∈ A) :
    ((a * b) * (a * b)) * x = x * ((a * b) * (a * b)) :=
  Sec51Tr.sq_comm (fun x hx y hy => H.ctx.setup.comm_A hx hy) H.ctx.setup.L_le H.ha2 H.hb2
    H.tr_a H.tr_b hx

theorem w_mem_normalizer_Abar (H : Sec51Bad A Abar S₀ B S h a b) :
    (a * b) * (a * b) ∈ normalizer (Abar : Set G) := by
  obtain ⟨-, -, -, hbw, -⟩ := sec51_dih4 H.ha2 H.hb2 H.hord
  exact mem_normalizer_of_commute_of_isTI H.ctx.setup.ti_Ab (H.ctx.setup.Lb_le H.hb) H.b_ne_one
    hbw.symm

theorem a_not_mem_normalizer (H : Sec51Bad A Abar S₀ B S h a b) :
    a ∉ normalizer (Abar : Set G) := by
  intro haN
  obtain ⟨hw1, -⟩ := sec51_dih4 H.ha2 H.hb2 H.hord
  have hb' : a * b * a⁻¹ ∈ Abar := by
    have := (Subgroup.mem_normalizer_iff.mp haN b).mp (H.ctx.setup.Lb_le H.hb)
    exact this
  have hw : (a * b) * (a * b) ∈ Abar := by
    have e : (a * b) * (a * b) = (a * b * a⁻¹) * (a * a * b) := by group
    rw [e, H.ha2, one_mul]
    exact Abar.mul_mem hb' (H.ctx.setup.Lb_le H.hb)
  exact hw1 (H.ctx.setup.eq_one_of_mem_Ab_of_centralizes hw fun x hx => H.w_centralizes hx)

theorem conj_a_ne (H : Sec51Bad A Abar S₀ B S h a b) : conjSubgroup a Abar ≠ Abar := fun e =>
  H.a_not_mem_normalizer (conjSubgroup_eq_self_iff.mp e)

theorem b_mem_normalizer_conj (H : Sec51Bad A Abar S₀ B S h a b) :
    b ∈ normalizer (conjSubgroup a Abar : Set G) := by
  obtain ⟨-, -, -, -, hab⟩ := sec51_dih4 H.ha2 H.hb2 H.hord
  have h1 : a * b * a ∈ normalizer (Abar : Set G) := by
    rw [hab]
    exact Subgroup.mul_mem _ H.w_mem_normalizer_Abar
      (Subgroup.le_normalizer (H.ctx.setup.Lb_le H.hb))
  have e : a * (a * b * a) * a⁻¹ = b := by
    calc a * (a * b * a) * a⁻¹ = (a * a) * b * (a * a⁻¹) := by group
      _ = b := by rw [H.ha2, one_mul, mul_inv_cancel, mul_one]
  have h2 : a * (a * b * a) * a⁻¹ ∈ conjSubgroup a (normalizer (Abar : Set G)) :=
    (mem_conjSubgroup_conj_t77 a _ _).2 h1
  rw [e, conjSubgroup_map_normalizer] at h2
  exact h2

theorem a_mem_S (H : Sec51Bad A Abar S₀ B S h a b) : a ∈ S := by
  obtain ⟨b', hb', rfl⟩ := (mem_conjSubgroup_exists_t77 h _ a).1 H.ha
  exact S.mul_mem (S.mul_mem H.hh (H.hAb0S hb')) (S.inv_mem H.hh)

theorem abar0_le_L (H : Sec51Bad A Abar S₀ B S h a b) {L L' M' : Subgroup G}
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') : Section3.Abar0 A Abar ≤ L := by
  intro β hβ
  by_contra hβL
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right H.ha2
  have hβĀ : β ∈ Abar := H.ctx.setup.Lb_le hβ
  have hβ'C : a * β * a⁻¹ ∈ conjSubgroup a Abar :=
    (mem_conjSubgroup_conj_t77 a β Abar).2 hβĀ
  have hβ'L' : a * β * a⁻¹ ∉ L' := by
    intro hmem
    apply hβL
    rw [P.mem_L]
    refine ⟨hβĀ, ?_⟩
    have h1 : a * β * a⁻¹ ∈ normalizer (Abar : Set G) := (P.mem_Lb.mp hmem).2
    rw [← conjSubgroup_map_normalizer, mem_conjSubgroup, hai]
    rwa [hai] at h1
  have hodd := P.odd_orderOf_mul hβĀ hβL hβ'C hβ'L'
  have haS : a ∈ S := H.a_mem_S
  have hβS : β ∈ S := H.hAb0S hβ
  have hmem : β * (a * β * a⁻¹) ∈ S :=
    S.mul_mem hβS (S.mul_mem (S.mul_mem haS hβS) (S.inv_mem haS))
  have h1 : β * (a * β * a⁻¹) = 1 := sec51_eq_one_of_odd H.hS hmem hodd
  have h2 : a * β * a⁻¹ = β⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : a * β * a⁻¹ ∈ Abar ⊓ conjSubgroup a Abar :=
    Subgroup.mem_inf.mpr ⟨by rw [h2]; exact Abar.inv_mem hβĀ, hβ'C⟩
  rw [P.inf_eq_bot, Subgroup.mem_bot, h2, inv_eq_one] at h3
  exact hβL (h3 ▸ L.one_mem)

theorem relIndex_abar0 (H : Sec51Bad A Abar S₀ B S h a b) :
    (Section3.Abar0 A Abar).relIndex Abar = 2 := by
  have := H.hq
  unfold Section3.q at this
  exact this

theorem L_eq (H : Sec51Bad A Abar S₀ B S h a b) {L L' M' : Subgroup G}
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') : L = Section3.Abar0 A Abar := by
  have hle := H.abar0_le_L P
  refine le_antisymm (fun e he => ?_) hle
  by_contra heAb0
  obtain ⟨β₀, hβ₀, hβ₀0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne H.ctx.setup.Lb_le
    H.ctx.setup.Lb_ne)
  have heĀ : e ∈ Abar := P.L_le he
  have hmul : β₀ * e ∈ Section3.Abar0 A Abar :=
    sa_mul_mem_of_index_two H.relIndex_abar0 hβ₀ heĀ hβ₀0 heAb0
  have hβ₀L : β₀ ∈ L := by
    have h1 : β₀ * e * e⁻¹ ∈ L := L.mul_mem (hle hmul) (L.inv_mem he)
    simpa using h1
  apply P.ne
  refine le_antisymm P.L_le (fun y hy => ?_)
  by_cases hyAb0 : y ∈ Section3.Abar0 A Abar
  · exact hle hyAb0
  · have hmul' : β₀ * y ∈ Section3.Abar0 A Abar :=
      sa_mul_mem_of_index_two H.relIndex_abar0 hβ₀ hy hβ₀0 hyAb0
    have h1 : β₀⁻¹ * (β₀ * y) ∈ L := L.mul_mem (L.inv_mem hβ₀L) (hle hmul')
    simpa using h1

theorem claim1 (H : Sec51Bad A Abar S₀ B S h a b) {α e : G} (hα : α ∈ A)
    (he : e ∈ Section3.Abar0 A Abar) :
    α * (a * e * a) * α⁻¹ = (α * e * α⁻¹ * e⁻¹) * (a * e * a) := by
  have hQ := H.ctx.setup
  have ha2 := H.ha2
  have hα2 : α * α = 1 := hQ.sq_A hα
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = α * e * α⁻¹ * e⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = a * α * a⁻¹ * α⁻¹ := ⟨_, rfl⟩
  have hκA0 : κ ∈ Section3.A0 A Abar := by
    rw [hκdef]
    exact hQ.commutator_mem_L hα he
  have hzA0 : z ∈ Section3.A0 A Abar := by
    rw [hzdef]
    exact H.tr_a.commutator_mem α hα
  have hαe : α * e * α = κ * e := by
    rw [hκdef, hαi]
    group
  have haα : a * α * a = z * α := by
    rw [hzdef, hai]
    group
  have key := sec51_claim1 ha2 hα2 (hQ.sq_A (hQ.L_le hzA0)) hαe haα
    (hQ.comm_M (hQ.L_le_M hκA0) (hQ.Lb_le_M he))
    (hQ.comm_M (hQ.L_le_M hzA0) (hQ.Lb_le_M he))
    (hQ.comm_A (hQ.L_le hzA0) (hQ.L_le hκA0)) (H.tr_a.comm_zero κ hκA0)
    (hQ.comm_A hα (hQ.L_le hzA0))
  rw [← hκdef, hαi]
  exact key

theorem centralizes_fixed (H : Sec51Bad A Abar S₀ B S h a b) {L L' M' : Subgroup G}
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') {m : G} (hm : m ∈ M')
    (hmA : ∀ x ∈ A, m * x = x * m) : a * m = m * a := by
  have hQ := H.ctx.setup
  have ha2 := H.ha2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hLeq := H.L_eq P
  obtain ⟨hLL', hL'L⟩ := sec51_swap_L ha2 P
  obtain ⟨e, heL, f, hfL', rfl⟩ := P.exists_mul_of_mem_M hm
  have he'L : a * f * a ∈ L := hL'L f hfL'
  obtain ⟨e', he'def⟩ : ∃ e', e' = a * f * a := ⟨_, rfl⟩
  rw [← he'def] at he'L
  have hfe' : f = a * e' * a := by
    rw [he'def]
    calc f = (a * a) * f * (a * a) := by rw [ha2]; group
      _ = a * (a * f * a) * a := by group
  have heAb0 : e ∈ Section3.Abar0 A Abar := hLeq ▸ heL
  have he'Ab0 : e' ∈ Section3.Abar0 A Abar := hLeq ▸ he'L
  have he2 : e * e = 1 := P.sq_A (P.L_le heL)
  have he'2 : e' * e' = 1 := P.sq_A (P.L_le he'L)
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have he'i : e'⁻¹ = e' := inv_eq_of_mul_eq_one_right he'2
  obtain ⟨α, hαA, hαA0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQ.L_le hQ.ne)
  have hα2 : α * α = 1 := hQ.sq_A hαA
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hκ : α * e * α⁻¹ * e⁻¹ ∈ Section3.A0 A Abar := hQ.commutator_mem_L hαA heAb0
  have hκ' : α * e' * α⁻¹ * e'⁻¹ ∈ Section3.A0 A Abar := hQ.commutator_mem_L hαA he'Ab0
  have hc1 := H.claim1 hαA he'Ab0
  rw [← hfe'] at hc1
  have hfix : α * (e * f) * α⁻¹ = e * f := by
    have := hmA α hαA
    calc α * (e * f) * α⁻¹ = (e * f) * α * α⁻¹ := by rw [this]
      _ = e * f := by group
  have hexp : α * (e * f) * α⁻¹ = (α * e * α⁻¹ * e⁻¹) * e * ((α * e' * α⁻¹ * e'⁻¹) * f) := by
    calc α * (e * f) * α⁻¹ = (α * e * α⁻¹) * (α * f * α⁻¹) := by group
      _ = (α * e * α⁻¹ * e⁻¹) * e * (α * f * α⁻¹) := by group
      _ = _ := by rw [hc1]
  set κ := α * e * α⁻¹ * e⁻¹ with hκdef
  set κ' := α * e' * α⁻¹ * e'⁻¹ with hκ'def
  have heκ' : e * κ' = κ' * e := (hQ.comm_M (hQ.L_le_M hκ') (hQ.Lb_le_M heAb0)).symm
  have h1 : κ * e * (κ' * f) = e * f := hexp.symm.trans hfix
  have h2 : (κ * κ') * (e * f) = e * f := by
    calc (κ * κ') * (e * f) = κ * (κ' * e) * f := by group
      _ = κ * (e * κ') * f := by rw [heκ']
      _ = κ * e * (κ' * f) := by group
      _ = e * f := h1
  have hκκ' : κ * κ' = 1 := mul_right_cancel (h2.trans (one_mul _).symm)
  have hee'comm : α * (e * e') = (e * e') * α := by
    have hα1 : α * e * α⁻¹ = κ * e := by rw [hκdef]; group
    have hα1' : α * e' * α⁻¹ = κ' * e' := by rw [hκ'def]; group
    have h3 : α * (e * e') * α⁻¹ = e * e' := by
      calc α * (e * e') * α⁻¹ = (α * e * α⁻¹) * (α * e' * α⁻¹) := by group
        _ = (κ * e) * (κ' * e') := by rw [hα1, hα1']
        _ = κ * (e * κ') * e' := by group
        _ = κ * (κ' * e) * e' := by rw [heκ']
        _ = (κ * κ') * (e * e') := by group
        _ = e * e' := by rw [hκκ', one_mul]
    calc α * (e * e') = α * (e * e') * α⁻¹ * α := by group
      _ = (e * e') * α := by rw [h3]
  have hmulAb0 : e * e' ∈ Section3.Abar0 A Abar := Subgroup.mul_mem _ heAb0 he'Ab0
  have hA0mem : e * e' ∈ Section3.A0 A Abar :=
    hQ.mem_L_of_commute_M hαA hαA0 (hQ.Lb_le_M hmulAb0) hee'comm
  have hee : e * e' = 1 := by
    have hmem : e * e' ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨hQ.L_le hA0mem, hQ.Lb_le hmulAb0⟩
    rw [hQ.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hee' : e' = e := (eq_inv_of_mul_eq_one_right hee).trans hei
  have hcomm_e : e * (a * e * a) = (a * e * a) * e := P.comm_L_Lb heL (hLL' e heL)
  have hconj : a * (e * (a * e * a)) * a = e * (a * e * a) := by
    calc a * (e * (a * e * a)) * a = a * e * a * e * (a * a) := by group
      _ = (a * e * a) * e := by rw [ha2, mul_one]
      _ = e * (a * e * a) := hcomm_e.symm
  rw [hfe', hee']
  calc a * (e * (a * e * a)) = a * (e * (a * e * a)) * a * a := by
        rw [mul_assoc _ a a, ha2, mul_one]
    _ = (e * (a * e * a)) * a := by rw [hconj]

theorem nonab_core (H : Sec51Bad A Abar S₀ B S h a b) {L L' M' : Subgroup G}
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') {g β : G}
    (hgM : g ∈ normalizer (M' : Set G)) (hβ : β ∈ Abar) (hβ0 : β ∉ Section3.Abar0 A Abar)
    (hcomm : a * (g⁻¹ * β * g) = (g⁻¹ * β * g) * a) : False := by
  have ha2 := H.ha2
  have hLeq := H.L_eq P
  obtain ⟨g₀, hg₀⟩ := H.ctx.exists_abar_eq
  have hQ := H.ctx.setup
  have hTel : IsElemAbelian 2 (conjSubgroup g⁻¹ Abar) := isElemAbelian_conj hQ.elem_Ab g⁻¹
  have hTTI : IsTI (conjSubgroup g⁻¹ Abar) := isTI_conjSubgroup hQ.ti_Ab g⁻¹
  have hβ1 : β ≠ 1 := fun e => hβ0 (e ▸ Subgroup.one_mem _)
  have hc₁T : g⁻¹ * β * g ∈ conjSubgroup g⁻¹ Abar := by
    have := (mem_conjSubgroup_conj_t77 g⁻¹ β Abar).2 hβ
    rwa [inv_inv] at this
  have hc₁1 : g⁻¹ * β * g ≠ 1 := by
    intro e
    exact hβ1 ((conj_eq_one_iff_t77 g⁻¹ β).1 (by rwa [inv_inv]))
  have haNT : a ∈ normalizer (conjSubgroup g⁻¹ Abar : Set G) :=
    mem_normalizer_of_commute_of_isTI hTTI hc₁T hc₁1 hcomm
  have haM : a ∈ normalizer (M' : Set G) := sec51_swap_M ha2 P
  have haT₀ := mem_normalizer_inf haNT haM
  have hconjL : ∀ y ∈ Abar, y ∈ Section3.Abar0 A Abar → g⁻¹ * y * g ∈
      conjSubgroup g⁻¹ Abar ⊓ M' := by
    intro y hy hy0
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := (mem_conjSubgroup_conj_t77 g⁻¹ y Abar).2 hy
      rwa [inv_inv] at this
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) y).mp
        (P.L_le_M (hLeq ▸ hy0))
      rwa [inv_inv] at this
  have hT₀ne : (conjSubgroup g⁻¹ Abar ⊓ M') ≠ ⊥ := by
    obtain ⟨ℓ, hℓ, hℓ1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot P.ne_bot
    intro hbot
    have hmem := hconjL ℓ (P.L_le hℓ) (hLeq ▸ hℓ)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hℓ1 ((conj_eq_one_iff_t77 g⁻¹ ℓ).1 (by rwa [inv_inv]))
  obtain ⟨t, htT₀, ht1, hat⟩ := exists_ne_one_commute
    (sec51_isElemAbelian_of_le hTel inf_le_left) hT₀ne haT₀ ha2
  have htT : t ∈ conjSubgroup g⁻¹ Abar := (Subgroup.mem_inf.mp htT₀).1
  have htM : t ∈ M' := (Subgroup.mem_inf.mp htT₀).2
  obtain ⟨hLL', hL'L⟩ := sec51_swap_L ha2 P
  have hinf : L ⊓ L' = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf P.L_le P.Lb_le) (le_of_eq P.inf_eq_bot))
  obtain ⟨e, heL, hte⟩ := sec51_fixed_decomp ha2 (fun x hx y hy => P.comm_L_Lb hx hy) hinf hLL'
    hL'L (by rw [← P.hM]; exact htM) hat
  have heAb0 : e ∈ Section3.Abar0 A Abar := hLeq ▸ heL
  have he2 : e * e = 1 := P.sq_A (P.L_le heL)
  have htA : ∀ x ∈ A, t * x = x * t := by
    intro x hx
    have h1 := Sec51Tr.sq_comm (fun x hx y hy => hQ.comm_A hx hy) hQ.L_le he2 ha2
      (hQ.tr_of_mem_Lb heAb0) H.tr_a hx
    have e1 : e * (a * e * a) = (e * a) * (e * a) := by group
    rw [hte, e1]
    exact h1
  have hAN : A ≤ normalizer (conjSubgroup g⁻¹ Abar : Set G) := fun x hx =>
    mem_normalizer_of_commute_of_isTI hTTI htT ht1 (htA x hx).symm
  have hTconj : conjSubgroup g⁻¹ Abar = conjSubgroup (g⁻¹ * g₀) A := by
    rw [hg₀, conjSubgroup_mul]
  have hTA : ∀ x ∈ conjSubgroup g⁻¹ Abar, ∀ y ∈ A, x * y = y * x :=
    sec51_comm_of_le_normalizer hTel hTTI (sec51_conj_of_conj hTconj) hAN
  have hkey : ∀ y ∈ Section3.Abar0 A Abar, a * (g⁻¹ * y * g) = (g⁻¹ * y * g) * a := by
    intro y hy0
    have hy : y ∈ Abar := hQ.Lb_le hy0
    have hmem := hconjL y hy hy0
    exact H.centralizes_fixed P (Subgroup.mem_inf.mp hmem).2
      (fun x hx => hTA _ (Subgroup.mem_inf.mp hmem).1 x hx)
  have hacT : ∀ x ∈ conjSubgroup g⁻¹ Abar, a * x = x * a := by
    intro x hx
    have hy : g * x * g⁻¹ ∈ Abar := by
      have := mem_conjSubgroup.mp hx
      rwa [inv_inv] at this
    have hxy : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    by_cases hy0 : g * x * g⁻¹ ∈ Section3.Abar0 A Abar
    · have := hkey _ hy0
      rwa [hxy] at this
    · have hmul : β * (g * x * g⁻¹) ∈ Section3.Abar0 A Abar :=
        sa_mul_mem_of_index_two H.relIndex_abar0 hβ hy hβ0 hy0
      have h1 := hkey _ hmul
      have e1 : g⁻¹ * (β * (g * x * g⁻¹)) * g = (g⁻¹ * β * g) * x := by group
      rw [e1] at h1
      exact sec51_cancel_comm hcomm h1
  have hV := H.v_ctx.setup
  have hTV : conjSubgroup g⁻¹ Abar ≤ normalizer (conjSubgroup h Abar : Set G) := fun x hx =>
    mem_normalizer_of_commute_of_isTI hV.ti_Ab H.a_mem_V H.a_ne_one (hacT x hx).symm
  have hVT : ∀ x ∈ conjSubgroup h Abar, ∀ y ∈ conjSubgroup g⁻¹ Abar, x * y = y * x := by
    refine sec51_comm_of_le_normalizer hV.elem_Ab hV.ti_Ab ⟨g⁻¹ * h⁻¹, ?_⟩ hTV
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  obtain ⟨x, hxX, hxeq⟩ := hV.exists_conj_eq
  have hAV := sec32b_root_contra H.ctx.hyp.rootTypeInCentralizer hxeq hxX
    (g := g⁻¹ * g₀) (by
      intro u hu y hy
      rw [← hTconj] at hy
      have hle : A ⊔ conjSubgroup h Abar ≤ centralizer (conjSubgroup g⁻¹ Abar : Set G) := by
        refine sup_le (fun v hv => ?_) (fun v hv => ?_)
        · exact Subgroup.mem_centralizer_iff.mpr fun y hy => hTA y hy v hv
        · exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hVT v hv y hy).symm
      exact (Subgroup.mem_centralizer_iff.mp (hle hu) y hy).symm) H.v_ctx.a0_ne_bot
  have hAN' : A ≤ normalizer (conjSubgroup h Abar : Set G) :=
    le_normalizer_of_comm fun u hu v hv => hAV u hu v hv
  apply H.v_ctx.a0_ne
  unfold Section3.A0 normalizerIn
  exact le_antisymm inf_le_left (le_inf le_rfl hAN')

theorem nonab_false (H : Sec51Bad A Abar S₀ B S h a b) {L L' M' : Subgroup G}
    (P : Prop24Setup Abar (conjSubgroup a Abar) L L' M') : False := by
  have ha2 := H.ha2
  have hLeq := H.L_eq P
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨β, hβĀ, hβ0⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne H.ctx.setup.Lb_le H.ctx.setup.Lb_ne)
  have hβL : β ∉ L := by
    rw [hLeq]
    exact hβ0
  have hβ'C : a * β * a ∈ conjSubgroup a Abar := by
    have := (mem_conjSubgroup_conj_t77 a β Abar).2 hβĀ
    rwa [hai] at this
  have hβ'L' : a * β * a ∉ L' := by
    intro hmem
    apply hβL
    rw [P.mem_L]
    refine ⟨hβĀ, ?_⟩
    have h1 := (P.mem_Lb.mp hmem).2
    rw [← conjSubgroup_map_normalizer, mem_conjSubgroup, hai]
    exact h1
  have hodd := P.odd_orderOf_mul hβĀ hβL hβ'C hβ'L'
  have hβ2 : β * β = 1 := P.sq_A hβĀ
  obtain ⟨-, hza, -, -, hg⟩ := sec51_dih_odd hβ2 ha2 hodd (by
    have e : (β * a) * (β * a) = β * (a * β * a) := by group
    rw [e])
  have hrM : β * a ∈ normalizer (M' : Set G) :=
    Subgroup.mul_mem _ (P.A_le_normalizer_M hβĀ) (sec51_swap_M ha2 P)
  have hgM : (β * a) ^ ((orderOf (β * (a * β * a)) + 1) / 2) ∈ normalizer (M' : Set G) :=
    Subgroup.pow_mem _ hrM _
  refine H.nonab_core P hgM hβĀ hβ0 ?_
  rw [hg]
  calc a * ((β * a) ^ orderOf (β * (a * β * a)) * a)
      = (a * (β * a) ^ orderOf (β * (a * β * a))) * a := (mul_assoc _ _ _).symm
    _ = ((β * a) ^ orderOf (β * (a * β * a)) * a) * a := by rw [← hza]

theorem prop24_nonab (H : Sec51Bad A Abar S₀ B S h a b)
    (hL : Abar ⊓ normalizer (conjSubgroup a Abar : Set G) ≠ Abar) :
    Prop24Setup Abar (conjSubgroup a Abar) (Abar ⊓ normalizer (conjSubgroup a Abar : Set G))
      (conjSubgroup a Abar ⊓ normalizer (Abar : Set G))
      ((Abar ⊓ normalizer (conjSubgroup a Abar : Set G)) ⊔
        (conjSubgroup a Abar ⊓ normalizer (Abar : Set G))) where
  elem := H.ctx.setup.elem_Ab
  ti := H.ctx.setup.ti_Ab
  conj := ⟨a, rfl⟩
  hL := rfl
  hLb := rfl
  hM := rfl
  ne_bot := by
    intro e
    have hb : b ∈ Abar ⊓ normalizer (conjSubgroup a Abar : Set G) :=
      Subgroup.mem_inf.mpr ⟨H.ctx.setup.Lb_le H.hb, H.b_mem_normalizer_conj⟩
    rw [e, Subgroup.mem_bot] at hb
    exact H.b_ne_one hb
  ne := hL

end Sec51Bad

end CFSG.RankThree.GF2n.Tim77
