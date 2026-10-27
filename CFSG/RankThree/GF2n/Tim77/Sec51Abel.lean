module

public import CFSG.RankThree.GF2n.Tim77.Sec51Basic
public import CFSG.RankThree.GF2n.Tim77.Sec46
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec51_isChoice_swap [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) :
    Section3.IsChoice Abar A := by
  obtain ⟨g₀, hg₀⟩ := h.exists_abar_eq
  have S := h.setup
  refine ⟨⟨g₀⁻¹, ?_⟩, ⟨h.a0_ne_bot, h.a0_ne⟩, ?_⟩
  · rw [hg₀, conjSubgroup_inv_conj_cancel]
  · intro g hg
    have e1 : conjSubgroup (g₀⁻¹ * (g * g₀)) A = conjSubgroup g₀⁻¹ (conjSubgroup g Abar) := by
      rw [conjSubgroup_mul, hg₀, ← conjSubgroup_mul g g₀ A]
    have e2 : conjSubgroup g₀⁻¹ Abar = A := by rw [hg₀, conjSubgroup_inv_conj_cancel]
    have hT : normalizerIn (conjSubgroup (g₀⁻¹ * (g * g₀)) A) A =
        conjSubgroup g₀⁻¹ (normalizerIn (conjSubgroup g Abar) Abar) := by
      have h3 := normalizerIn_conjSubgroup_t77 g₀⁻¹ (conjSubgroup g Abar) Abar
      rw [e2] at h3
      rw [e1]
      exact h3
    obtain ⟨hne1, hne2⟩ := hg
    have hne1' : normalizerIn (conjSubgroup (g₀⁻¹ * (g * g₀)) A) A ≠ ⊥ := by
      rw [hT]
      intro e
      exact hne1 ((conjSubgroup_eq_bot_t77 g₀⁻¹ _).1 e)
    have hne2' : normalizerIn (conjSubgroup (g₀⁻¹ * (g * g₀)) A) A ≠
        conjSubgroup (g₀⁻¹ * (g * g₀)) A := by
      rw [hT, e1]
      intro e
      exact hne2 (conjSubgroup_inj_t77 g₀⁻¹ e)
    have hm := h.nota.choice.2.2 (g₀⁻¹ * (g * g₀)) ⟨hne1', hne2'⟩
    rw [hT, card_conjSubgroup] at hm
    calc Nat.card (normalizerIn (conjSubgroup g Abar) Abar)
        ≤ Nat.card (Section3.Abar0 A Abar) := hm
      _ = Nat.card (Section3.A0 A Abar) := S.card_Lb_eq

theorem sec51_q_swap [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) :
    Section3.q Abar A = Section3.q A Abar := by
  unfold Section3.q
  exact h.setup.relIndex_Lb.symm

theorem sec51_swap_ctx [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {S' B' : Subgroup G} (hS'2 : IsPGroup 2 S') (hS'N : S' ≤ normalizer (Abar : Set G))
    (hS'max : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (Abar : Set G) → S' ≤ T → T = S')
    (hcont : Abar ⊔ Section3.A0 A Abar ≤ S') (hconj : ∃ g : G, B' = conjSubgroup g Abar)
    (hne : B' ≠ Abar) (hle : B' ≤ S' ⊓ centralizer (Abar : Set G)) : Sec3Ctx Abar A S' B' := by
  obtain ⟨g₀, hg₀⟩ := h.exists_abar_eq
  have hc := h.conj g₀
  rw [← hg₀] at hc
  exact ⟨hc.hyp, hc.not_root, hc.not_wc,
    ⟨sec51_isChoice_swap h, ⟨hS'2, hS'N, hS'max⟩, hcont, hconj, hne, hle⟩⟩

theorem sec51_A0_le_C [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) :
    Section3.A0 A Abar ≤ normalizer (conjSubgroup a Abar : Set G) := by
  intro y hy
  rw [← conjSubgroup_eq_self_iff]
  have hya : y * a = a * y := (hTr.comm_zero y hy).symm
  have hyAb : conjSubgroup y Abar = Abar := conjSubgroup_eq_self_iff.mpr (Subgroup.mem_inf.mp hy).2
  rw [← conjSubgroup_mul, hya, conjSubgroup_mul, hyAb]

theorem sec51_ab_ctx [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a : G} (hTr : Sec51Tr A (Section3.A0 A Abar) a) (hne : conjSubgroup a Abar ≠ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    ∃ S' : Subgroup G, Sec3Ctx Abar A S' (conjSubgroup a Abar) := by
  have hQ := h.setup
  have hCel : IsElemAbelian 2 (conjSubgroup a Abar) := isElemAbelian_conj hQ.elem_Ab a
  have hCTI : IsTI (conjSubgroup a Abar) := isTI_conjSubgroup hQ.ti_Ab a
  have hAbN : Abar ≤ normalizer (conjSubgroup a Abar : Set G) :=
    le_normalizer_of_comm fun x hx y hy => hcomm x hx y hy
  have hCN : conjSubgroup a Abar ≤ normalizer (Abar : Set G) :=
    le_normalizer_of_comm fun y hy x hx => (hcomm x hx y hy).symm
  have hA0Ab : Section3.A0 A Abar ≤ normalizer (Abar : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp hx).2
  have hA0C : Section3.A0 A Abar ≤ normalizer (conjSubgroup a Abar : Set G) :=
    sec51_A0_le_C h hTr
  have hE : IsElemAbelian 2 (Abar ⊔ conjSubgroup a Abar) := by
    have := tim77_2_3 hCel hCTI (g := a⁻¹) (by rw [conjSubgroup_inv_conj_cancel]; exact hAbN)
    rw [conjSubgroup_inv_conj_cancel, sup_comm] at this
    exact this
  have hEA0 : Section3.A0 A Abar ≤
      normalizer ((Abar ⊔ conjSubgroup a Abar : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_sup (hA0Ab hy) (hA0C hy)
  have hT2 : IsPGroup 2 ((Abar ⊔ conjSubgroup a Abar) ⊔ Section3.A0 A Abar : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (notation_isPGroup_two_of_le hE le_rfl)
      (notation_isPGroup_two_of_le hQ.elem hQ.L_le) hEA0
  have hTN : (Abar ⊔ conjSubgroup a Abar) ⊔ Section3.A0 A Abar ≤ normalizer (Abar : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hCN) hA0Ab
  obtain ⟨Qs, hQs⟩ := notation_exists_sylow_le hT2 hTN
  obtain ⟨hS2, hSN, hSmax⟩ := notation_sylow_map_max Qs
  refine ⟨_, sec51_swap_ctx h hS2 hSN hSmax ?_ ⟨a, rfl⟩ hne ?_⟩
  · exact le_trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hQs
  · intro y hy
    refine Subgroup.mem_inf.mpr ⟨(le_sup_right.trans le_sup_left |>.trans hQs) hy, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy

theorem sec51_order_two_or_four {y : G} (h4 : y ^ 4 = 1) (h1 : y ≠ 1) :
    orderOf y = 2 ∨ orderOf y = 4 := by
  have hdvd : orderOf y ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact orderOf_dvd_of_pow_eq_one h4
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases i
  · exact absurd (orderOf_eq_one_iff.1 (by simpa using hord)) h1
  · exact Or.inl (by simpa using hord)
  · exact Or.inr (by simpa using hord)

theorem sec51_ab_choice [Finite G]
    {A Abar S' C : Subgroup G} (h' : Sec3Ctx Abar A S' C)
    (hq' : Section3.q Abar A = 2) (hCel : IsElemAbelian 2 C) (hAel : IsElemAbelian 2 A)
    (hA0C : Section3.A0 A Abar ≤ normalizer (C : Set G)) (hAC : A ⊓ C = ⊥) :
    ∃ b' ∈ C, b' ∉ normalizer ((Abar ⊔ A : Subgroup G) : Set G) ∧
      Section3.IsSChoice Abar A S' C b' ∧ ¬ Group.IsSolvable ↥(Section3.Y Abar A b') := by
  obtain ⟨b', hb'C, hb'N⟩ := SetLike.not_le_iff_exists.mp
    (tim77Sec35_holds G Abar A S' C h')
  have hb'1 : b' ≠ 1 := fun e => hb'N (e ▸ Subgroup.one_mem _)
  obtain ⟨x, hx, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot h'.setup.Lb_ne_bot
  have hxA : x ∈ A := (Subgroup.mem_inf.mp hx).1
  have hxx : x * x = 1 := by rw [← pow_two]; exact hAel.2 x hxA
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxC : x * b' * x⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hA0C hx) b').mp hb'C
  have hsq : (x * b') ^ 2 ∈ C := by
    have e : (x * b') ^ 2 = (x * b' * x⁻¹) * b' := by rw [hxi, pow_two]; group
    rw [e]
    exact C.mul_mem hxC hb'C
  have h4 : (x * b') ^ 4 = 1 := by
    have := hCel.2 _ hsq
    rwa [← pow_mul] at this
  have hxb1 : x * b' ≠ 1 := by
    intro e
    have hxb : x = b'⁻¹ := eq_inv_of_mul_eq_one_left e
    have : x ∈ A ⊓ C := Subgroup.mem_inf.mpr ⟨hxA, by rw [hxb]; exact C.inv_mem hb'C⟩
    rw [hAC, Subgroup.mem_bot] at this
    exact hx1 this
  have hs : Section3.IsSChoice Abar A S' C b' :=
    ⟨b', hb'C, hb'1, Or.inl ⟨⟨x, hx, hx1, sec51_order_two_or_four h4 hxb1⟩, rfl⟩⟩
  refine ⟨b', hb'C, hb'N, hs, fun hsolv => ?_⟩
  exact hb'N (mem_normalizer_X_of_Y_eq h' hb'C (sec43_of G Abar A S' C b' h' hs hq' hsolv))

theorem sec51_ab_x_eq {a β a₀ ε : G} (ha : a * a = 1) (hβ : β * β = 1)
    (haa₀ : a * a₀ = a₀ * a) (hβa₀ : β * a₀ * β = ε * a₀)
    (hβε : β * (a * ε * a) = (a * ε * a) * β) :
    (β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹ = a * ε * a * (ε * a₀) := by
  rw [sec51_h0_inv ha hβ]
  calc β * (a * β * a) * a₀ * (a * β * a * β)
      = β * (a * β * a * a₀ * (a * β * a)) * β := by simp only [mul_assoc]
    _ = β * (a * ε * a * a₀) * β := by rw [sec51_h0_conj ha haa₀ hβa₀]
    _ = β * (a * ε * a) * a₀ * β := by simp only [mul_assoc]
    _ = a * ε * a * β * a₀ * β := by rw [hβε]
    _ = a * ε * a * (β * a₀ * β) := by simp only [mul_assoc]
    _ = a * ε * a * (ε * a₀) := by rw [hβa₀]

theorem sec51_ab_eps [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {β a₀ : G}
    (hβ : β ∈ Abar) (ha₀ : a₀ ∈ Section3.A0 A Abar) :
    β * a₀ * β⁻¹ * a₀⁻¹ ∈ Section3.Abar0 A Abar ∧
      β * a₀ * β = (β * a₀ * β⁻¹ * a₀⁻¹) * a₀ := by
  have hQ := h.setup
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ2
  have ha₀i : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right (hQ.sq_A (hQ.L_le ha₀))
  refine ⟨hQ.commutator_mem_Lb hβ ha₀, ?_⟩
  have ha₀2 : a₀ * a₀ = 1 := hQ.sq_A (hQ.L_le ha₀)
  rw [hβi, ha₀i]
  calc β * a₀ * β = β * a₀ * β * (a₀ * a₀) := by rw [ha₀2, mul_one]
    _ = (β * a₀ * β * a₀) * a₀ := by group

theorem sec51_ab_h0 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a β : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) {a₀ α : G}
    (ha₀ : a₀ ∈ Section3.A0 A Abar) (hα : α ∈ A) :
    α * ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) =
      ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) * α := by
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hα2 : α * α = 1 := hQ.sq_A hα
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have ha₀A : a₀ ∈ A := hQ.L_le ha₀
  obtain ⟨hεmem, hβa₀⟩ := sec51_ab_eps h hβ ha₀
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = β * a₀ * β⁻¹ * a₀⁻¹ := ⟨_, rfl⟩
  rw [← hεdef] at hεmem hβa₀
  have hε2 : ε * ε = 1 := hQ.sq_Ab (hQ.Lb_le hεmem)
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = α * ε * α⁻¹ * ε⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = a * α * a⁻¹ * α⁻¹ := ⟨_, rfl⟩
  have hκ : κ ∈ Section3.A0 A Abar := by
    rw [hκdef]
    exact hQ.commutator_mem_L hα hεmem
  have hz : z ∈ Section3.A0 A Abar := by
    rw [hzdef]
    exact hTr.commutator_mem α hα
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε2
  have hαε : α * ε * α = κ * ε := by
    rw [hκdef, hαi, hεi]
    calc α * ε * α = α * ε * α * (ε * ε) := by rw [hε2, mul_one]
      _ = (α * ε * α * ε) * ε := by group
  have haα : a * α * a = z * α := by
    rw [hzdef, hai]
    group
  have hβC : ∀ y ∈ Abar, β * (a * y * a) = (a * y * a) * β := fun y hy => by
    have hy' : a * y * a⁻¹ ∈ conjSubgroup a Abar := (mem_conjSubgroup_conj_t77 a y Abar).2 hy
    rw [hai] at hy'
    exact hcomm β hβ _ hy'
  exact sec51_h0_centralizes ha2 hβ2 hα2 (hQ.sq_A (hQ.L_le hκ)) (hQ.sq_A (hQ.L_le hz))
    (hTr.comm_zero a₀ ha₀) (hTr.comm_zero κ hκ) hβa₀ hαε haα
    (hQ.comm_M (hQ.L_le_M hκ) (hQ.Lb_le_M hεmem))
    (hQ.comm_M (hQ.L_le_M hz) (hQ.Lb_le_M hεmem))
    (hQ.comm_A (hQ.L_le hz) (hQ.L_le hκ))
    (hQ.comm_A hα ha₀A) (hQ.comm_A hα (hQ.L_le hz)) (hβC ε (hQ.Lb_le hεmem))

theorem sec51_ab_not_mem [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a β : G} (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hβN : β ∉ normalizer (A : Set G)) (hne : conjSubgroup a Abar ≠ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    (β * (a * β * a)) ∉ normalizer (A : Set G) := by
  intro hN
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  obtain ⟨a₀, ha₀, ha₀1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hQ.ne_bot
  have ha₀A : a₀ ∈ A := hQ.L_le ha₀
  obtain ⟨hεmem, hβa₀⟩ := sec51_ab_eps h hβ ha₀
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = β * a₀ * β⁻¹ * a₀⁻¹ := ⟨_, rfl⟩
  rw [← hεdef] at hεmem hβa₀
  have hεĀ : ε ∈ Abar := hQ.Lb_le hεmem
  have hβC : ∀ y ∈ Abar, β * (a * y * a) = (a * y * a) * β := fun y hy => by
    have hy' : a * y * a⁻¹ ∈ conjSubgroup a Abar := (mem_conjSubgroup_conj_t77 a y Abar).2 hy
    rw [hai] at hy'
    exact hcomm β hβ _ hy'
  have hβε := hβC ε hεĀ
  have hx := sec51_ab_x_eq ha2 hβ2 (hTr.comm_zero a₀ ha₀) hβa₀ hβε
  have hxA : (β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hN a₀).mp ha₀A
  rw [hx] at hxA
  have htA : a * ε * a * ε ∈ A := by
    have h1 := A.mul_mem hxA (A.inv_mem ha₀A)
    have e : a * ε * a * (ε * a₀) * a₀⁻¹ = a * ε * a * ε := by group
    rwa [e] at h1
  have hβεcomm : β * ε = ε * β := h.setup_symm.comm_A hβ hεĀ
  have htβ : β * (a * ε * a * ε) = (a * ε * a * ε) * β := by
    calc β * (a * ε * a * ε) = (β * (a * ε * a)) * ε := by group
      _ = ((a * ε * a) * β) * ε := by rw [hβε]
      _ = (a * ε * a) * (β * ε) := by group
      _ = (a * ε * a) * (ε * β) := by rw [hβεcomm]
      _ = (a * ε * a * ε) * β := by group
  have ht1 : a * ε * a * ε = 1 := by
    by_contra ht1
    exact hβN (hQ.mem_Lb.mp (hQ.mem_Lb_of_commute hβ htA ht1 htβ)).2
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right (hQ.sq_Ab hεĀ)
  have hae : a * ε * a = ε := by
    have h1 : a * ε * a = ε⁻¹ := eq_inv_of_mul_eq_one_left ht1
    rw [h1, hεi]
  have hεC : a * ε * a ∈ conjSubgroup a Abar := by
    have := (mem_conjSubgroup_conj_t77 a ε Abar).2 hεĀ
    rwa [hai] at this
  have hε1 : ε = 1 := by
    have hmem : ε ∈ Abar ⊓ conjSubgroup a Abar := Subgroup.mem_inf.mpr ⟨hεĀ, hae ▸ hεC⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI hQ.ti_Ab hne, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hε1, one_mul] at hβa₀
  have hβa : β * a₀ = a₀ * β := by
    calc β * a₀ = β * a₀ * β * β := by rw [mul_assoc _ β β, hβ2, mul_one]
      _ = a₀ * β := by rw [hβa₀]
  exact hβN (hQ.mem_Lb.mp (hQ.mem_Lb_of_commute hβ ha₀A ha₀1 hβa)).2

theorem sec51_ab_comm [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a β : G} (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    ∀ α ∈ A, ∀ α' ∈ A, α * ((β * (a * β * a)) * α' * (β * (a * β * a))⁻¹) =
      ((β * (a * β * a)) * α' * (β * (a * β * a))⁻¹) * α := by
  have hQ := h.setup
  obtain ⟨a₀, ha₀, ha₀1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hQ.ne_bot
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, h₀ = β * (a * β * a) := ⟨_, rfl⟩
  rw [← hh₀]
  have hA₁TI : IsTI (conjSubgroup h₀ A) := isTI_conjSubgroup h.hyp.ti h₀
  have hA₁el : IsElemAbelian 2 (conjSubgroup h₀ A) := isElemAbelian_conj h.hyp.elemAbelian h₀
  have hxA₁ : h₀ * a₀ * h₀⁻¹ ∈ conjSubgroup h₀ A :=
    (mem_conjSubgroup_conj_t77 h₀ a₀ A).2 (hQ.L_le ha₀)
  have hx1 : h₀ * a₀ * h₀⁻¹ ≠ 1 := fun e => ha₀1 ((conj_eq_one_iff_t77 h₀ a₀).1 e)
  have hAN : A ≤ normalizer (conjSubgroup h₀ A : Set G) := fun α hα =>
    mem_normalizer_of_commute_of_isTI hA₁TI hxA₁ hx1 (by
      rw [hh₀]
      exact sec51_ab_h0 h hTr ha2 hβ hcomm ha₀ hα)
  have hcomm' := sec51_comm_of_le_normalizer hA₁el hA₁TI
    ⟨h₀⁻¹, (conjSubgroup_inv_conj_cancel h₀ A).symm⟩ hAN
  intro α hα α' hα'
  exact (hcomm' _ ((mem_conjSubgroup_conj_t77 h₀ α' A).2 hα') α hα).symm

theorem sec51_A_inf_C [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a : G}
    (haN : a ∈ normalizer (A : Set G)) : A ⊓ conjSubgroup a Abar = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
  have h1 : a⁻¹ * x * a ∈ Abar := mem_conjSubgroup.mp hxC
  have h2 : a⁻¹ * x * a ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) x).mp hxA
    simpa using this
  have h3 : a⁻¹ * x * a ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨h2, h1⟩
  rw [h.setup.inf_eq_bot, Subgroup.mem_bot] at h3
  have : x = 1 := by
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [h3]; group
  exact this

theorem sec51_ab_PC [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) :
    ∃ M : Subgroup G, Prop24Setup A (conjSubgroup a Abar) (Section3.A0 A Abar)
      (conjSubgroup a (Section3.Abar0 A Abar)) M := by
  have hAN : conjSubgroup a A = A := conjSubgroup_eq_self_iff.mpr hTr.mem_normalizer
  have hA0 : conjSubgroup a (Section3.A0 A Abar) = Section3.A0 A Abar := by
    ext x
    rw [mem_conjSubgroup]
    constructor
    · intro hx
      have h1 := hTr.comm_zero _ hx
      have e : x = a⁻¹ * x * a := by
        calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
          _ = (a⁻¹ * x * a) * a * a⁻¹ := by rw [h1]
          _ = a⁻¹ * x * a := by group
      rw [e]
      exact hx
    · intro hx
      have h1 := hTr.comm_zero x hx
      have e : a⁻¹ * x * a = x := by
        calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
          _ = a⁻¹ * (a * x) := by rw [h1]
          _ = x := by group
      rw [e]
      exact hx
  have hc := (h.conj a).setup
  rw [section3_A0_conj, section3_Abar0_conj, hAN, hA0] at hc
  exact ⟨_, hc⟩

theorem sec51_ab_conj_le [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a β : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hβ : β ∈ Abar) :
    conjSubgroup (a * β * a) (Section3.A0 A Abar) ≤ normalizer (A : Set G) := by
  have hQ := h.setup
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 (a * β * a) _ y).1 hy
  obtain ⟨hεmem, hβx⟩ := sec51_ab_eps h hβ hx
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hb'2 : (a * β * a) * (a * β * a) = 1 := by
    calc (a * β * a) * (a * β * a) = a * β * (a * a) * β * a := by group
      _ = a * (β * β) * a := by rw [ha2, mul_one]; group
      _ = 1 := by rw [hβ2, mul_one, ha2]
  rw [inv_eq_of_mul_eq_one_right hb'2, sec51_h0_conj ha2 (hTr.comm_zero x hx) hβx]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hTr.mem_normalizer
    (hQ.mem_Lb.mp hεmem).2) hTr.mem_normalizer) (Subgroup.le_normalizer (hQ.L_le hx))

theorem sec51_ab_D [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a β α : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hβN : β ∉ normalizer (A : Set G)) (hα : α ∈ A) (hαA0 : α ∉ Section3.A0 A Abar) :
    (a * β * a) ∈ Section3.Y Abar A (a * β * a) ∧ α ∈ Section4.D Abar A (a * β * a) ∧
      β ∈ Section4.D Abar A (a * β * a) ∧ (a * β * a) ∈ Section4.D Abar A (a * β * a) := by
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hα2 : α * α = 1 := hQ.sq_A hα
  obtain ⟨b', hb'def⟩ : ∃ b', b' = a * β * a := ⟨_, rfl⟩
  rw [← hb'def]
  have hb'2 : b' * b' = 1 := by
    rw [hb'def]
    calc (a * β * a) * (a * β * a) = a * β * (a * a) * β * a := by group
      _ = a * (β * β) * a := by rw [ha2, mul_one]; group
      _ = 1 := by rw [hβ2, mul_one, ha2]
  have hb'i : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'2
  have hb'C : b' ∈ conjSubgroup a Abar := by
    have := (mem_conjSubgroup_conj_t77 a β Abar).2 hβ
    rwa [hai, ← hb'def] at this
  have hAY : A ≤ Section3.Y Abar A b' := le_sup_right.trans le_sup_left
  have hĀY : Abar ≤ Section3.Y Abar A b' := le_sup_left.trans le_sup_left
  have hconjY : conjSubgroup b' A ≤ Section3.Y Abar A b' := le_sup_right
  have hβ0 : β ∉ Section3.A0 Abar A := fun hm => hβN (Subgroup.mem_inf.mp hm).2
  have hβ0' : β ∉ Section3.Abar0 A Abar := fun hm => hβN (Subgroup.mem_inf.mp hm).2
  have hβD : β ∈ Section4.D Abar A b' :=
    sec41_mem_D.mpr ⟨1, one_mem _, β, hβ, hβ0, by simp⟩
  have hodd1 : Odd (orderOf (β * α)) := h.setup_symm.odd_orderOf_mul hβ hβ0' hα hαA0
  obtain ⟨k, hk⟩ := sec51_conj_of_odd hβ2 hα2 hodd1
  have hyY : (β * α) ^ k ∈ Section3.Y Abar A b' :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (hĀY hβ) (hAY hα)) k
  have hαD : α ∈ Section4.D Abar A b' :=
    sec41_mem_D.mpr ⟨((β * α) ^ k)⁻¹, Subgroup.inv_mem _ hyY, β, hβ, hβ0, by rw [inv_inv, hk]⟩
  obtain ⟨M, PC⟩ := sec51_ab_PC h hTr
  have hb'0 : b' ∉ conjSubgroup a (Section3.Abar0 A Abar) := by
    intro hm
    apply hβN
    have h1 := mem_conjSubgroup.mp hm
    have e : a⁻¹ * b' * a = β := by
      rw [hb'def, hai]
      calc a * (a * β * a) * a = (a * a) * β * (a * a) := by group
        _ = β := by rw [ha2]; group
    rw [e] at h1
    exact (hQ.mem_Lb.mp h1).2
  have hodd2 : Odd (orderOf (α * b')) := PC.odd_orderOf_mul hα hαA0 hb'C hb'0
  have hsq : (α * b') ^ 2 ∈ Section3.Y Abar A b' := by
    have e : (α * b') ^ 2 = α * (b' * α * b'⁻¹) := by
      rw [pow_two, hb'i]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hAY hα) (hconjY ((mem_conjSubgroup_conj_t77 b' α A).2 hα))
  have hαb'Y : α * b' ∈ Section3.Y Abar A b' := qp_mem_of_sq_mem_of_odd hsq hodd2
  have hb'Y : b' ∈ Section3.Y Abar A b' := by
    have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAY hα)) hαb'Y
    simpa using h1
  obtain ⟨k', hk'⟩ := sec51_conj_of_odd hα2 hb'2 hodd2
  have hb'D : b' ∈ Section4.D Abar A b' := by
    have h1 := sec41_D_conj (Subgroup.inv_mem _ (Subgroup.pow_mem _ hαb'Y k')) hαD
    rwa [inv_inv, hk'] at h1
  exact ⟨hb'Y, hαD, hβD, hb'D⟩

theorem sec51_bender_data [Finite G]
    {A Abar S₀ B : Subgroup G} {s : G} (h : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) (hsolv : ¬ Group.IsSolvable ↥(Section3.Y A Abar s))
    [((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] :
    Sec42Data ↥(Section3.Y A Abar s) ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
        {t | (t : G) ∈ Section4.D A Abar s} ∧
      CFSG.BenderSuzuki.IsBenderGroup
        ((↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸
          Subgroup.center (↥(Section3.Y A Abar s) ⧸
            (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) := by
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨-, hcomm2⟩ := sec32b_of tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨hcls, hRI, hne4, hcent⟩ := sec41_of tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hdat := sa_sec42Data h hs hcomm2 hRI hne4 hcls hcent
  have hns : ¬ Group.IsSolvable (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) :=
    sec44w_not_solvable_quot (fun x hx y hy => Subtype.ext (hNc _ (Subgroup.mem_subgroupOf.mp hx)
      _ (Subgroup.mem_subgroupOf.mp hy))) hsolv
  obtain ⟨-, hB⟩ := qp_main hdat hns
  exact ⟨hdat, hB⟩

theorem sec51_quot_contra {W : Type} [Group W] [Finite W] {N₀ : Subgroup W} [N₀.Normal]
    {D₀ : Set W} (hdat : Sec42Data W N₀ D₀)
    (hB : CFSG.BenderSuzuki.IsBenderGroup ((W ⧸ N₀) ⧸ Subgroup.center (W ⧸ N₀)))
    {p u v : W} (hp : p ∈ D₀) (hu : u ∈ D₀) (hv : v ∈ D₀) (huv : u * v = v * u)
    (hne : u * v ∉ N₀)
    (hpc : p * (u * v * p * (u * v)⁻¹) = (u * v * p * (u * v)⁻¹) * p)
    (hodd : Odd (orderOf (u * p))) (hup : u * p ∉ N₀) : False := by
  set ι : W →* ((W ⧸ N₀) ⧸ Subgroup.center (W ⧸ N₀)) :=
    (QuotientGroup.mk' (Subgroup.center (W ⧸ N₀))).comp (QuotientGroup.mk' N₀) with hι
  have hord : ∀ {t : W}, t ∈ D₀ → orderOf (ι t) = 2 := fun {t} ht => sec46_orderOf_two hdat hB ht
  have hD : ∀ {t : W}, t ∈ D₀ → QuotientGroup.mk' N₀ t ∈ QuotientGroup.mk' N₀ '' D₀ :=
    fun {t} ht => ⟨t, ht, rfl⟩
  have huu : u * u = 1 := by rw [← pow_two]; exact hdat.invol u hu
  have hvv : v * v = 1 := by rw [← pow_two]; exact hdat.invol v hv
  refine sec51_bender_contra hB (hord hp) (hord hu) (hord hv)
    (Commute.map (show Commute u v from huv) ι) ?_ ?_ ?_
  ·
    intro hεq
    apply hne
    have h1 : (QuotientGroup.mk' N₀ u)⁻¹ * QuotientGroup.mk' N₀ v ∈
        Subgroup.center (W ⧸ N₀) := QuotientGroup.eq.mp hεq
    by_cases h1' : (QuotientGroup.mk' N₀ u)⁻¹ * QuotientGroup.mk' N₀ v = 1
    · have h2 : QuotientGroup.mk' N₀ u = QuotientGroup.mk' N₀ v := inv_mul_eq_one.mp h1'
      have h3 : (QuotientGroup.mk' N₀ (u * v)) = 1 := by
        rw [map_mul, ← h2, ← map_mul, huu, map_one]
      exact (QuotientGroup.eq_one_iff _).mp h3
    · exfalso
      refine qp_inj hdat (hD hu) h1 h1' ?_
      rw [mul_inv_cancel_left]
      exact hD hv
  ·
    have := Commute.map (show Commute p (u * v * p * (u * v)⁻¹) from hpc) ι
    simpa [map_mul, map_inv] using this
  ·
    intro hc
    have hc2 : Commute (QuotientGroup.mk' N₀ p) (QuotientGroup.mk' N₀ u) :=
      qp_commute_lift_Z hdat (hD hp) (hD hu) hc
    apply hup
    refine qp_mem_of_sq_mem_of_odd ?_ hodd
    have := qp_sq_mem hdat hu hp hc2.symm
    exact this

theorem sec51_abelian_contra [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {a : G}
    (hTr : Sec51Tr A (Section3.A0 A Abar) a) (ha2 : a * a = 1) (hne : conjSubgroup a Abar ≠ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) : False := by
  have hQ := h.setup
  have haN : a ∈ normalizer (A : Set G) := hTr.mem_normalizer
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨S', h'⟩ := sec51_ab_ctx h hTr hne hcomm
  have hq' : Section3.q Abar A = 2 := (sec51_q_swap h).trans hq
  have hCel : IsElemAbelian 2 (conjSubgroup a Abar) := isElemAbelian_conj hQ.elem_Ab a
  have hAC : A ⊓ conjSubgroup a Abar = ⊥ := sec51_A_inf_C h haN
  have hCN : conjSubgroup a Abar ≤ normalizer (Abar : Set G) :=
    le_normalizer_of_comm fun y hy x hx => (hcomm x hx y hy).symm
  obtain ⟨b', hb'C, hb'N, hs, hsolv⟩ :=
    sec51_ab_choice h' hq' hCel h.hyp.elemAbelian (sec51_A0_le_C h hTr) hAC
  obtain ⟨β, hβdef⟩ : ∃ β, β = a * b' * a := ⟨_, rfl⟩
  have hb'eq : a * β * a = b' := by
    rw [hβdef]
    calc a * (a * b' * a) * a = (a * a) * b' * (a * a) := by group
      _ = b' := by rw [ha2]; group
  have hβĀ : β ∈ Abar := by
    have := mem_conjSubgroup.mp hb'C
    rwa [hai, ← hβdef] at this
  have hβN : β ∉ normalizer (A : Set G) := by
    intro hβ
    apply hb'N
    have hb'A : b' ∈ normalizer (A : Set G) := by
      rw [← hb'eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hβ) haN
    exact mem_normalizer_sup (hCN hb'C) hb'A
  obtain ⟨α, hαA, hαA0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQ.L_le hQ.ne)
  obtain ⟨hb'Y, hαD, hβD, hb'D⟩ := sec51_ab_D h hTr ha2 hβĀ hβN hαA hαA0
  rw [hb'eq] at hb'Y hαD hβD hb'D
  have hAY : A ≤ Section3.Y Abar A b' := le_sup_right.trans le_sup_left
  have hĀY : Abar ≤ Section3.Y Abar A b' := le_sup_left.trans le_sup_left
  have hαY : α ∈ Section3.Y Abar A b' := hAY hαA
  have hβY : β ∈ Section3.Y Abar A b' := hĀY hβĀ
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G Abar A S' (conjSubgroup a Abar) b' h' hs
  haveI hNn : ((Section3.N Abar A b').subgroupOf (Section3.Y Abar A b')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr fun y hy => hYN y hy
  obtain ⟨hdat, hB⟩ := sec51_bender_data h' hs hsolv
  have hN'le : Section3.N Abar A b' ≤ normalizer (A : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).2
    · intro x hx
      exact Subgroup.le_normalizer (Subgroup.mem_inf.mp hx).1
    · have := sec51_ab_conj_le h hTr ha2 hβĀ
      rw [hb'eq] at this
      exact this
  have hnm := sec51_ab_not_mem h hTr ha2 hβĀ hβN hne hcomm
  rw [hb'eq] at hnm
  have hcomm' := sec51_ab_comm h hTr ha2 hβĀ hcomm α hαA α hαA
  rw [hb'eq] at hcomm'
  have hodd : Odd (orderOf (β * α)) :=
    h.setup_symm.odd_orderOf_mul hβĀ (fun hm => hβN (Subgroup.mem_inf.mp hm).2) hαA hαA0
  refine sec51_quot_contra hdat hB (p := ⟨α, hαY⟩) (u := ⟨β, hβY⟩) (v := ⟨b', hb'Y⟩)
    hαD hβD hb'D (Subtype.ext (hcomm β hβĀ b' hb'C)) ?_ (Subtype.ext hcomm') ?_ ?_
  · intro hm
    exact hnm (hN'le (Subgroup.mem_subgroupOf.mp hm))
  · rw [show (⟨β, hβY⟩ * ⟨α, hαY⟩ : ↥(Section3.Y Abar A b')) = ⟨β * α, mul_mem hβY hαY⟩ from rfl,
      Subgroup.orderOf_mk]
    exact hodd
  · intro hm
    have h1 := hN'le (Subgroup.mem_subgroupOf.mp hm)
    apply hβN
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.le_normalizer hαA))
    simpa using h2

end CFSG.RankThree.GF2n.Tim77
