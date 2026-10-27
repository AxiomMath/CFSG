module

public import CFSG.RankThree.GF2n.Tim77.Sec51Abel
public import CFSG.RankThree.GF2n.Tim77.Sec53Hyp

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec53e_A0_le_C [Finite G] {A Abar : Subgroup G} {a : G}
    (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G)) :
    Section3.A0 A Abar ≤ normalizer (conjSubgroup a Abar : Set G) := by
  intro y hy
  rw [← conjSubgroup_eq_self_iff]
  have hy' : a⁻¹ * y * a ∈ Section3.A0 A Abar := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN0) y).mp hy
    simpa using this
  have hyAb : conjSubgroup (a⁻¹ * y * a) Abar = Abar :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.mem_inf.mp hy').2
  have e : y * a = a * (a⁻¹ * y * a) := by group
  rw [← conjSubgroup_mul, e, conjSubgroup_mul, hyAb]

theorem sec53e_ab_ctx [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a : G} (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (hne : conjSubgroup a Abar ≠ Abar)
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
    sec53e_A0_le_C haN0
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

theorem sec53e_ab_PC [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G)) :
    ∃ M : Subgroup G, Prop24Setup A (conjSubgroup a Abar) (Section3.A0 A Abar)
      (conjSubgroup a (Section3.Abar0 A Abar)) M := by
  have hAN : conjSubgroup a A = A := conjSubgroup_eq_self_iff.mpr haN
  have hA0 : conjSubgroup a (Section3.A0 A Abar) = Section3.A0 A Abar :=
    conjSubgroup_eq_self_iff.mpr haN0
  have hc := (h.conj a).setup
  rw [section3_A0_conj, section3_Abar0_conj, hAN, hA0] at hc
  exact ⟨_, hc⟩

theorem sec53e_comm_mem [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hqA : (Section3.A0 A Abar).relIndex A = 2) {a : G} (haN : a ∈ normalizer (A : Set G))
    (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G)) {α : G} (hα : α ∈ A) :
    a * α * a⁻¹ * α⁻¹ ∈ Section3.A0 A Abar := by
  have hQ := h.setup
  have hαi : α⁻¹ ∈ A := A.inv_mem hα
  have haαA : a * α * a⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp haN α).mp hα
  by_cases hα0 : α ∈ Section3.A0 A Abar
  · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp haN0 α).mp hα0)
      (Subgroup.inv_mem _ hα0)
  · have h1 : a * α * a⁻¹ ∉ Section3.A0 A Abar := by
      intro hm
      apply hα0
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN0) _).mp hm
      simpa [mul_assoc] using this
    have h2 : α⁻¹ ∉ Section3.A0 A Abar := fun hm => hα0 (by simpa using Subgroup.inv_mem _ hm)
    exact sec53_mul_mem_of_relIndex_two (fun x hx y hy => hQ.comm_A hx hy)
      (fun x hx => hQ.sq_A hx) hqA haαA hαi h1 h2

theorem sec53e_ab_conj_le [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a β : G} (haN : a ∈ normalizer (A : Set G))
    (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G)) (ha2 : a * a = 1) (hβ : β ∈ Abar) :
    conjSubgroup (a * β * a) (Section3.A0 A Abar) ≤ normalizer (A : Set G) := by
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_conjSubgroup_exists_t77 (a * β * a) _ y).1 hy
  have hx' : a * x * a ∈ Section3.A0 A Abar := by
    have := (Subgroup.mem_normalizer_iff.mp haN0 x).mp hx
    rwa [hai] at this
  obtain ⟨hεmem, hβx⟩ := sec51_ab_eps h hβ hx'
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hb'2 : (a * β * a) * (a * β * a) = 1 := by
    calc (a * β * a) * (a * β * a) = a * β * (a * a) * β * a := by group
      _ = a * (β * β) * a := by rw [ha2, mul_one]; group
      _ = 1 := by rw [hβ2, mul_one, ha2]
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = β * (a * x * a) * β⁻¹ * (a * x * a)⁻¹ := ⟨_, rfl⟩
  rw [← hεdef] at hεmem hβx
  have e : (a * β * a) * x * (a * β * a) = (a * ε * a) * x := by
    calc (a * β * a) * x * (a * β * a) = a * (β * (a * x * a) * β) * a := by
          simp only [mul_assoc]
      _ = a * (ε * (a * x * a)) * a := by rw [hβx]
      _ = (a * ε * a) * x * (a * a) := by simp only [mul_assoc]
      _ = (a * ε * a) * x := by rw [ha2, mul_one]
  rw [inv_eq_of_mul_eq_one_right hb'2, e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haN
    (hQ.mem_Lb.mp hεmem).2) haN) (Subgroup.le_normalizer (hQ.L_le hx))

theorem sec53e_ab_D [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {a β α : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) (hβ : β ∈ Abar) (hβN : β ∉ normalizer (A : Set G)) (hα : α ∈ A)
    (hαA0 : α ∉ Section3.A0 A Abar) :
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
  obtain ⟨M, PC⟩ := sec53e_ab_PC h haN haN0
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

theorem sec53e_ab_not_mem [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {a β a₀ : G} (ha₀ : a₀ ∈ Section3.A0 A Abar) (ha₀1 : a₀ ≠ 1) (ha₀a : a * a₀ * a = a₀)
    (ha2 : a * a = 1) (hβ : β ∈ Abar) (hβN : β ∉ normalizer (A : Set G))
    (hne : conjSubgroup a Abar ≠ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x) :
    (β * (a * β * a)) ∉ normalizer (A : Set G) := by
  intro hN
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have ha₀A : a₀ ∈ A := hQ.L_le ha₀
  have haa₀ : a * a₀ = a₀ * a := by
    calc a * a₀ = a * a₀ * a * a := by rw [mul_assoc _ a a, ha2, mul_one]
      _ = a₀ * a := by rw [ha₀a]
  obtain ⟨hεmem, hβa₀⟩ := sec51_ab_eps h hβ ha₀
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = β * a₀ * β⁻¹ * a₀⁻¹ := ⟨_, rfl⟩
  rw [← hεdef] at hεmem hβa₀
  have hεĀ : ε ∈ Abar := hQ.Lb_le hεmem
  have hβC : ∀ y ∈ Abar, β * (a * y * a) = (a * y * a) * β := fun y hy => by
    have hy' : a * y * a⁻¹ ∈ conjSubgroup a Abar := (mem_conjSubgroup_conj_t77 a y Abar).2 hy
    rw [hai] at hy'
    exact hcomm β hβ _ hy'
  have hβε := hβC ε hεĀ
  have hx := sec51_ab_x_eq ha2 hβ2 haa₀ hβa₀ hβε
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

theorem sec53e_ab_h0 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hqA : (Section3.A0 A Abar).relIndex A = 2) {a β a₀ α : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x)
    (ha₀ : a₀ ∈ Section3.A0 A Abar) (ha₀a : a * a₀ * a = a₀)
    (hκ : ∀ α ∈ A, ∀ β ∈ Abar,
      a * (α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) * a =
        α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀))
    (hα : α ∈ A) :
    α * ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) =
      ((β * (a * β * a)) * a₀ * (β * (a * β * a))⁻¹) * α := by
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hβ2 : β * β = 1 := hQ.sq_Ab hβ
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ2
  have hα2 : α * α = 1 := hQ.sq_A hα
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have ha₀A : a₀ ∈ A := hQ.L_le ha₀
  have ha₀2 : a₀ * a₀ = 1 := hQ.sq_A ha₀A
  have ha₀i : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
  have haa₀ : a * a₀ = a₀ * a := by
    calc a * a₀ = a * a₀ * a * a := by rw [mul_assoc _ a a, ha2, mul_one]
      _ = a₀ * a := by rw [ha₀a]
  obtain ⟨hεmem, hβa₀⟩ := sec51_ab_eps h hβ ha₀
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = β * a₀ * β⁻¹ * a₀⁻¹ := ⟨_, rfl⟩
  rw [← hεdef] at hεmem hβa₀
  have hε2 : ε * ε = 1 := hQ.sq_Ab (hQ.Lb_le hεmem)
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε2
  have hεe : ε = β * a₀ * β * a₀ := by rw [hεdef, hβi, ha₀i]
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = α * ε * α⁻¹ * ε⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = a * α * a⁻¹ * α⁻¹ := ⟨_, rfl⟩
  have hκmem : κ ∈ Section3.A0 A Abar := by
    rw [hκdef]
    exact hQ.commutator_mem_L hα hεmem
  have hz : z ∈ Section3.A0 A Abar := by
    rw [hzdef]
    exact sec53e_comm_mem h hqA haN haN0 hα
  have hκeq : κ = α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀) := by
    rw [hκdef, hαi, hεi, ← hεe]
  have haκ : a * κ = κ * a := by
    have h1 := hκ α hα β hβ
    rw [← hκeq] at h1
    calc a * κ = a * κ * a * a := by rw [mul_assoc _ a a, ha2, mul_one]
      _ = κ * a := by rw [h1]
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
  exact sec51_h0_centralizes ha2 hβ2 hα2 (hQ.sq_A (hQ.L_le hκmem)) (hQ.sq_A (hQ.L_le hz))
    haa₀ haκ hβa₀ hαε haα
    (hQ.comm_M (hQ.L_le_M hκmem) (hQ.Lb_le_M hεmem))
    (hQ.comm_M (hQ.L_le_M hz) (hQ.Lb_le_M hεmem))
    (hQ.comm_A (hQ.L_le hz) (hQ.L_le hκmem))
    (hQ.comm_A hα ha₀A) (hQ.comm_A hα (hQ.L_le hz)) (hβC ε (hQ.Lb_le hεmem))

theorem sec53e_ab_comm [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hqA : (Section3.A0 A Abar).relIndex A = 2) {a β a₀ : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) (hβ : β ∈ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x)
    (ha₀ : a₀ ∈ Section3.A0 A Abar) (ha₀1 : a₀ ≠ 1) (ha₀a : a * a₀ * a = a₀)
    (hκ : ∀ α ∈ A, ∀ β ∈ Abar,
      a * (α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) * a =
        α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) :
    ∀ α ∈ A, ∀ α' ∈ A, α * ((β * (a * β * a)) * α' * (β * (a * β * a))⁻¹) =
      ((β * (a * β * a)) * α' * (β * (a * β * a))⁻¹) * α := by
  have hQ := h.setup
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
      exact sec53e_ab_h0 h hqA haN haN0 ha2 hβ hcomm ha₀ ha₀a hκ hα)
  have hcomm' := sec51_comm_of_le_normalizer hA₁el hA₁TI
    ⟨h₀⁻¹, (conjSubgroup_inv_conj_cancel h₀ A).symm⟩ hAN
  intro α hα α' hα'
  exact (hcomm' _ ((mem_conjSubgroup_conj_t77 h₀ α' A).2 hα') α hα).symm

theorem sec53_elem_contra
    [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {a : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) (hne : conjSubgroup a Abar ≠ Abar)
    (hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x)
    {a₀ : G} (ha₀ : a₀ ∈ Section3.A0 A Abar) (ha₀1 : a₀ ≠ 1) (ha₀a : a * a₀ * a = a₀)
    (hκ : ∀ α ∈ A, ∀ β ∈ Abar,
      a * (α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) * a =
        α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) : False := by
  have hQ := h.setup
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨S', h'⟩ := sec53e_ab_ctx h haN0 hne hcomm
  have hq' : Section3.q Abar A = 2 := (sec51_q_swap h).trans hq
  have hqA : (Section3.A0 A Abar).relIndex A = 2 := hq'
  have hCel : IsElemAbelian 2 (conjSubgroup a Abar) := isElemAbelian_conj hQ.elem_Ab a
  have hAC : A ⊓ conjSubgroup a Abar = ⊥ := sec51_A_inf_C h haN
  have hCN : conjSubgroup a Abar ≤ normalizer (Abar : Set G) :=
    le_normalizer_of_comm fun y hy x hx => (hcomm x hx y hy).symm
  obtain ⟨b', hb'C, hb'N, hs, hsolv⟩ :=
    sec51_ab_choice h' hq' hCel h.hyp.elemAbelian (sec53e_A0_le_C haN0) hAC
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
  obtain ⟨hb'Y, hαD, hβD, hb'D⟩ := sec53e_ab_D h haN haN0 ha2 hβĀ hβN hαA hαA0
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
    · have := sec53e_ab_conj_le h haN haN0 ha2 hβĀ
      rw [hb'eq] at this
      exact this
  have hnm := sec53e_ab_not_mem h ha₀ ha₀1 ha₀a ha2 hβĀ hβN hne hcomm
  rw [hb'eq] at hnm
  have hcomm' := sec53e_ab_comm h hqA haN haN0 ha2 hβĀ hcomm ha₀ ha₀1 ha₀a hκ α hαA α hαA
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
