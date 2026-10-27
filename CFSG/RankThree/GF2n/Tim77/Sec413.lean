module

public import CFSG.RankThree.GF2n.Tim77.Sec3Conj

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup

theorem sec413_of (h412 : Tim77Sec412Statement) :
    ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
      Section3.q A Abar = 2 → Sec4A0LeCenterH A Abar →
        ∀ a ∈ A, a ∉ Section3.A0 A Abar → ∀ g : G, ∀ y ∈ A, y ∉ Section3.A0 A Abar →
          orderOf (a * (g * y * g⁻¹)) ≠ 4 := by
  intro G _ _ A Abar S₀ B h hq hc a ha haA0 g y hy hyA0 hord
  generalize hx : g * y * g⁻¹ = x at hord
  have hxA : x ∈ conjSubgroup g A := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, ← hx,
      show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  have hxA0 : x ∉ Section3.A0 (conjSubgroup g A) (conjSubgroup g Abar) := by
    rw [section3_A0_conj, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, ← hx,
      show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hyA0
  have hxN : x ∈ normalizer (A : Set G) := h412 G A Abar S₀ B h hq hc a ha haA0 g x hxA hord
  have hcS : Sec3Ctx (conjSubgroup g A) (conjSubgroup g Abar) (conjSubgroup g S₀)
      (conjSubgroup g B) := h.conj g
  have hqS : Section3.q (conjSubgroup g A) (conjSubgroup g Abar) = 2 := by
    rw [section3_q_conj]; exact hq
  have hcS' : Sec4A0LeCenterH (conjSubgroup g A) (conjSubgroup g Abar) := by
    rw [sec4A0LeCenterH_conj_iff]; exact hc
  have hA' : conjSubgroup g⁻¹ (conjSubgroup g A) = A := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]
  have haA' : a ∈ conjSubgroup g⁻¹ (conjSubgroup g A) := by
    rw [hA']; exact ha
  have hswap : orderOf (x * a) = orderOf (a * x) := by
    have hinj := orderOf_injective (MulAut.conj a⁻¹).toMonoidHom (MulEquiv.injective _) (a * x)
    have e : (MulAut.conj a⁻¹).toMonoidHom (a * x) = x * a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e] at hinj
    exact hinj
  have haN : a ∈ normalizer ((conjSubgroup g A : Subgroup G) : Set G) :=
    h412 G (conjSubgroup g A) (conjSubgroup g Abar) (conjSubgroup g S₀) (conjSubgroup g B)
      hcS hqS hcS' x hxA hxA0 g⁻¹ a haA' (hswap.trans hord)
  have hc1 : x * a⁻¹ * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hxN a⁻¹).1 (A.inv_mem ha)
  have hc2 : a * x * a⁻¹ ∈ conjSubgroup g A := (Subgroup.mem_normalizer_iff.1 haN x).1 hxA
  have hcomm : a * x = x * a := by
    by_cases hbot : A ⊓ conjSubgroup g A = ⊥
    · have hmem : a * (x * a⁻¹ * x⁻¹) ∈ A ⊓ conjSubgroup g A := by
        refine Subgroup.mem_inf.2 ⟨A.mul_mem ha hc1, ?_⟩
        have e : a * (x * a⁻¹ * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by group
        rw [e]
        exact (conjSubgroup g A).mul_mem hc2 ((conjSubgroup g A).inv_mem hxA)
      rw [hbot, Subgroup.mem_bot] at hmem
      calc a * x = (a * (x * a⁻¹ * x⁻¹)) * (x * a) := by group
        _ = x * a := by rw [hmem, one_mul]
    · have hAg : conjSubgroup g A = A :=
        CFSG.RankThree.GF2n.conjSubgroup_eq_of_isTI h.hyp.ti hbot
      have hxA' : x ∈ A := by
        rw [← hAg]; exact hxA
      have hcommA := h.hyp.elemAbelian.1.is_comm.comm (⟨a, ha⟩ : A) ⟨x, hxA'⟩
      exact congrArg Subtype.val hcommA
  have ha2 : a ^ 2 = 1 := h.hyp.elemAbelian.2 a ha
  have hy2 : y ^ 2 = 1 := h.hyp.elemAbelian.2 y hy
  have hx2 : x ^ 2 = 1 := by
    have hconj2 : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by
      simp only [pow_two, mul_assoc, inv_mul_cancel_left]
    rw [← hx, hconj2, hy2]
    simp
  have hsq : (a * x) ^ 2 = 1 := by
    rw [Commute.mul_pow (show Commute a x from hcomm) 2, ha2, hx2, one_mul]
  have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [hord] at hdvd
  omega

end CFSG.RankThree.GF2n.Tim77
