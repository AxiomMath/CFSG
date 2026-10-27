module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def M23InvCentOrd : Prop :=
  ∀ t : NativeSporadic.Carrier .M23, orderOf t = 2 →
    Nat.card (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier .M23))) = 2688

@[expose] def M24InvCentOrd : Prop :=
  ∀ t : NativeSporadic.Carrier .M24, orderOf t = 2 →
    Nat.card (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier .M24))) = 21504 ∨
      Nat.card (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier .M24))) = 7680

theorem fixSub_conj {G : Type*} [Group G] (t : G) :
    fixSub (MulAut.conj t) = Subgroup.centralizer ({t} : Set G) := by
  ext x
  rw [mem_fixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem invol_apply {L : Type*} [Group L] {β : MulAut L} (h2 : β ^ 2 = 1) (z : L) :
    β (β z) = z := by
  have h := congrArg (fun φ : MulAut L => φ z) h2
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
  exact h

theorem card_fixSub_transport {L X : Type} [Group L] [Group X] (e : L ≃* X) (β : MulAut L) :
    Nat.card (fixSub β) = Nat.card (fixSub (e.symm.trans (β.trans e))) := by
  have hmap : (fixSub β).map e.toMonoidHom = fixSub (e.symm.trans (β.trans e)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [mem_fixSub] at hx ⊢
      show e (β (e.symm (e x))) = e x
      rw [MulEquiv.symm_apply_apply, hx]
    · intro hy
      rw [mem_fixSub] at hy
      refine Subgroup.mem_map.2 ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [mem_fixSub]
      apply e.injective
      rw [e.apply_symm_apply]
      exact hy
  rw [← hmap]
  exact Nat.card_congr (e.subgroupMap (fixSub β)).toEquiv

theorem m22_fixSub_card_not_dvd (L : Type) [Group L] [Finite L]
    (e : L ≃* NativeSporadic.Carrier .M22) (β : MulAut L) (h1 : β ≠ 1) :
    ¬ 443520 ∣ Nat.card (fixSub β) := by
  have hM : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Schreier.m22_card
  have hL : Nat.card L = 443520 := by rw [Nat.card_congr e.toEquiv, hM]
  have hne : fixSub β ≠ ⊤ := by
    intro htop
    apply h1
    refine MulEquiv.ext (fun x => ?_)
    have hx : x ∈ fixSub β := by rw [htop]; exact Subgroup.mem_top x
    rw [mem_fixSub] at hx
    rw [MulAut.one_apply, hx]
  have hle := Subgroup.card_le_card_group (fixSub β)
  rw [hL] at hle
  have hlt : Nat.card (fixSub β) < 443520 := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq (fixSub β) (by rw [h, hL])) hne
  have hpos : 0 < Nat.card (fixSub β) := Nat.card_pos
  intro hd
  exact absurd (Nat.le_of_dvd hpos hd) (by omega)

theorem m23_all_inner
    (β' : MulAut (NativeSporadic.Carrier .M23)) :
    ∃ t : NativeSporadic.Carrier .M23, ∀ y, β' y = t * y * t⁻¹ := by
  haveI : Finite (NativeSporadic.Carrier .M23) := CFSG.Sporadic.Mathieu.fam_m23_simplicity.1
  have hc : Subgroup.center (NativeSporadic.Carrier .M23) = ⊥ := m23_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m23_mulAut_card
  have hmem : β' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (NativeSporadic.Carrier .M23) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, fun y => by rw [← ht]; simp [MulAut.conj_apply]⟩

theorem m24_all_inner
    (β' : MulAut (NativeSporadic.Carrier .M24)) :
    ∃ t : NativeSporadic.Carrier .M24, ∀ y, β' y = t * y * t⁻¹ := by
  haveI : Finite (NativeSporadic.Carrier .M24) := CFSG.Sporadic.Mathieu.fam_m24_simplicity.1
  have hc : Subgroup.center (NativeSporadic.Carrier .M24) = ⊥ := m24_center_eq_bot'
  have htop := inner_eq_top_of_card_le hc m24_mulAut_card
  have hmem : β' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (NativeSporadic.Carrier .M24) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, fun y => by rw [← ht]; simp [MulAut.conj_apply]⟩

theorem invol_of_conj {X : Type} [Group X] (hc : Subgroup.center X = ⊥) (t : X)
    (h2 : ∀ y, t * (t * y * t⁻¹) * t⁻¹ = y) (h1 : ∃ y, t * y * t⁻¹ ≠ y) :
    t ^ 2 = 1 ∧ t ≠ 1 := by
  have hc' : t ^ 2 ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : t ^ 2 * y * (t ^ 2)⁻¹ = y := by
      calc t ^ 2 * y * (t ^ 2)⁻¹ = t * (t * y * t⁻¹) * t⁻¹ := by rw [pow_two]; group
        _ = y := h2 y
    rw [mul_inv_eq_iff_eq_mul] at hy
    exact hy.symm
  have hsq : t ^ 2 = 1 := by
    rw [hc] at hc'
    exact Subgroup.mem_bot.1 hc'
  refine ⟨hsq, fun ht => ?_⟩
  obtain ⟨y, hy⟩ := h1
  exact hy (by rw [ht]; group)

theorem m23_fixSub_card_not_dvd
    (hC : M23InvCentOrd) (L : Type) [Group L] (e : L ≃* NativeSporadic.Carrier .M23)
    (β : MulAut L) (h2 : β ^ 2 = 1) (h1 : β ≠ 1) : ¬ 443520 ∣ Nat.card (fixSub β) := by
  have hfin : Finite (NativeSporadic.Carrier .M23) := CFSG.Sporadic.Mathieu.fam_m23_simplicity.1
  have hβX2 : (e.symm.trans (β.trans e)) ^ 2 = 1 := by
    refine MulEquiv.ext (fun y => ?_)
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    show e (β (e.symm (e (β (e.symm y))))) = y
    rw [MulEquiv.symm_apply_apply, invol_apply h2, e.apply_symm_apply]
  have hβX1 : e.symm.trans (β.trans e) ≠ 1 := by
    intro h
    apply h1
    refine MulEquiv.ext (fun x => ?_)
    have hx : e.symm.trans (β.trans e) (e x) = e x := by rw [h]; rfl
    have h' : e (β (e.symm (e x))) = e x := hx
    rw [MulEquiv.symm_apply_apply] at h'
    rw [MulAut.one_apply]
    exact e.injective h'
  obtain ⟨t, ht⟩ := m23_all_inner (e.symm.trans (β.trans e))
  have hcen : Subgroup.center (NativeSporadic.Carrier .M23) = ⊥ := m23_center_eq_bot'
  have hsq : ∀ y, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    have h := invol_apply hβX2 y
    rw [ht, ht] at h
    exact h
  have hne : ∃ y, t * y * t⁻¹ ≠ y := by
    by_contra hcon
    push_neg at hcon
    apply hβX1
    refine MulEquiv.ext (fun y => ?_)
    rw [MulAut.one_apply, ht]
    exact hcon y
  obtain ⟨ht2, ht1⟩ := invol_of_conj hcen t hsq hne
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hβconj : e.symm.trans (β.trans e) = MulAut.conj t :=
    MulEquiv.ext (fun y => by rw [MulAut.conj_apply]; exact ht y)
  rw [card_fixSub_transport e β, hβconj, fixSub_conj, hC t hord]
  norm_num

theorem m24_fixSub_card_not_dvd
    (hC : M24InvCentOrd) (L : Type) [Group L] (e : L ≃* NativeSporadic.Carrier .M24)
    (β : MulAut L) (h2 : β ^ 2 = 1) (h1 : β ≠ 1) : ¬ 443520 ∣ Nat.card (fixSub β) := by
  have hfin : Finite (NativeSporadic.Carrier .M24) := CFSG.Sporadic.Mathieu.fam_m24_simplicity.1
  have hβX2 : (e.symm.trans (β.trans e)) ^ 2 = 1 := by
    refine MulEquiv.ext (fun y => ?_)
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    show e (β (e.symm (e (β (e.symm y))))) = y
    rw [MulEquiv.symm_apply_apply, invol_apply h2, e.apply_symm_apply]
  have hβX1 : e.symm.trans (β.trans e) ≠ 1 := by
    intro h
    apply h1
    refine MulEquiv.ext (fun x => ?_)
    have hx : e.symm.trans (β.trans e) (e x) = e x := by rw [h]; rfl
    have h' : e (β (e.symm (e x))) = e x := hx
    rw [MulEquiv.symm_apply_apply] at h'
    rw [MulAut.one_apply]
    exact e.injective h'
  obtain ⟨t, ht⟩ := m24_all_inner (e.symm.trans (β.trans e))
  have hcen : Subgroup.center (NativeSporadic.Carrier .M24) = ⊥ := m24_center_eq_bot'
  have hsq : ∀ y, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    have h := invol_apply hβX2 y
    rw [ht, ht] at h
    exact h
  have hne : ∃ y, t * y * t⁻¹ ≠ y := by
    by_contra hcon
    push_neg at hcon
    apply hβX1
    refine MulEquiv.ext (fun y => ?_)
    rw [MulAut.one_apply, ht]
    exact hcon y
  obtain ⟨ht2, ht1⟩ := invol_of_conj hcen t hsq hne
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hβconj : e.symm.trans (β.trans e) = MulAut.conj t :=
    MulEquiv.ext (fun y => by rw [MulAut.conj_apply]; exact ht y)
  rw [card_fixSub_transport e β, hβconj, fixSub_conj]
  rcases hC t hord with h | h <;> rw [h] <;> norm_num

end CFSG.Quasithin.H13.Ch4

end
