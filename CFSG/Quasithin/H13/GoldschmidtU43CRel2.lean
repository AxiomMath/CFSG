module

public import CFSG.Quasithin.H13.GoldschmidtU43CRel
public import CFSG.Quasithin.H13.GoldschmidtU43CQ8

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem sq_conj_of_sq {z : G} (g x : ↥(Hz z)) (hx : x * x = zK z) :
    (g⁻¹ * x * g) ^ 2 = zK z := by
  rw [pow_two]
  calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    _ = g⁻¹ * zK z * g := by rw [hx]
    _ = zK z := by rw [← zK_comm g⁻¹]; group

theorem jw13_of_data [Finite G] {z : G} (h : Hyp z) {R : Subgroup ↥(Hz z)} (hR : SylR h R)
    {u u' σ₁ : ↥(Hz z)} {a : ↥(Uz z)} {n₁ : V4}
    (hu : u ∈ Subgroup.normalizer (R : Set ↥(Hz z)))
    (hu' : u' ∈ Subgroup.normalizer (R : Set ↥(Hz z)))
    (hu2 : u * u = 1) (hu'2 : u' * u' = 1) (hcomm : u * u' * u⁻¹ * u'⁻¹ = zK z)
    (hp : SwapPairA (h.act u) (h.act u'))
    (hσR : σ₁ ∈ R) (hρfix : ∀ v, InP2 v → vapp (h.act σ₁) v = v)
    (hn₁ : InP1 n₁) (hn₁0 : n₁ ≠ 0) (hcn₁ : vapp (h.act u * h.act u') n₁ = n₁)
    (hrefl : ∀ ξ, InP1 ξ → ξ ≠ 0 → ξ ≠ n₁ → vapp (h.act u * h.act u') ξ = ξ + n₁)
    (ha : h.tv a = n₁) (hsign : conjU σ₁⁻¹ (conjU σ₁⁻¹ a) = a * conjU σ₁⁻¹ a) :
    JW13 (uK a) σ₁ u (u * u') := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hu'i : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'2
  have hvi : (u * u')⁻¹ = u' * u := by rw [mul_inv_rev, hui, hu'i]
  have hv2 : (u * u') * (u * u') = zK z := by
    have := hcomm
    rw [hui, hu'i] at this
    calc u * u' * (u * u') = u * u' * u * u' := by simp only [mul_assoc]
      _ = zK z := this
  have hvN : u * u' ∈ Subgroup.normalizer (R : Set ↥(Hz z)) := mul_mem hu hu'
  have hqa : q (h.tv a) = 1 := by
    rw [ha]
    exact q_plane1 n₁ hn₁ hn₁0
  have hA2 : uK a * uK a = zK z := by
    rw [← uK_mul, h.mul_self_of_q_one hqa]
    rfl
  have hsi : h.act u⁻¹ = h.act u := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hp.2.2.1
  obtain ⟨n', hn'1, hn'0, hn'n⟩ := exists_other_plane1 n₁ hn₁ hn₁0
  obtain ⟨j, hj⟩ := h.tv_surj n'
  have hR3' : (u * u') * uK a * (u * u')⁻¹ = (uK a)⁻¹ := by
    have key := h.conjU_refl (u * u') hv2 (a := a) (j := j) hqa
      (by rw [map_mul, ha]; exact hcn₁)
      (by
        rw [map_mul, hj, ha, hrefl n' hn'1 hn'0 hn'n, add_comm])
    have e := (uK_conjU (u * u') a).symm.trans (congrArg uK key)
    exact e
  have hσ₂R : u⁻¹ * σ₁ * u ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hu) σ₁).mp hσR
    simpa using this
  have hactσ₂ : h.act (u⁻¹ * σ₁ * u) = h.act u * h.act σ₁ * h.act u := by
    rw [map_mul, map_mul, hsi]
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : ↥(Hz z), σ₂ = u⁻¹ * σ₁ * u := ⟨_, rfl⟩
  have hσ₂R' : σ₂ ∈ R := by rw [hσ₂]; exact hσ₂R
  have hactσ₂' : h.act σ₂ = h.act u * h.act σ₁ * h.act u := by rw [hσ₂]; exact hactσ₂
  refine ⟨hR.pow_three hσR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [sq_conj_of_sq σ₁ (uK a) hA2, pow_two, hA2]
  ·
    rw [conj_inv_eq h hv2, hR3']
  ·
    have := congrArg uK hsign
    rw [uK_conjU, uK_mul, uK_conjU] at this
    simpa only [inv_inv] using this
  ·
    rw [sq_conj_of_sq u (uK a) hA2, pow_two, hA2]
  ·
    have hR3'' : (u * u') * uK a * (u' * u) = (uK a)⁻¹ := by rw [← hvi]; exact hR3'
    have hrhs : (u⁻¹ * uK a * u)⁻¹ = u * (uK a)⁻¹ * u := by
      simp only [mul_inv_rev, hui, mul_assoc]
    rw [hrhs, hui, hvi]
    calc u' * u * (u * uK a * u) * (u * u') = u' * (u * u) * uK a * (u * u) * u' := by group
      _ = u' * uK a * u' := by rw [hu2]; group
      _ = (u * u) * u' * uK a * u' * (u * u) := by rw [hu2]; group
      _ = u * ((u * u') * uK a * (u' * u)) * u := by group
      _ = u * (uK a)⁻¹ * u := by rw [hR3'']
  ·
    rw [← hσ₂, conj_inv_eq h hv2]
    have hσ₂W : h.act σ₂ ∈ Rbar := h.mem_Wsub.1 (hR.le_W hσ₂R')
    have hlhs : (u * u') * σ₂ * (u * u')⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hvN _).mp hσ₂R'
    refine hR.act_inj' hlhs (R.inv_mem hσ₂R') ?_
    simp only [map_mul, map_inv]
    exact cprime_invA (h.act_mem_Oq u) (h.act_mem_Oq u') hp hσ₂W
  ·
    have hP2 : InP2 (h.tv (conjU u⁻¹ a)) := by
      rw [h.tv_conj, hsi, ha]
      exact hp.1.1 n₁ hn₁
    have hc := h.comm_tv a (conjU u⁻¹ a)
    rw [show bq (h.tv a) (h.tv (conjU u⁻¹ a)) = 0 by rw [ha]; exact perp_planes _ _ hn₁ hP2,
      zp_zero] at hc
    have hc' : (a : G) * (conjU u⁻¹ a : G) = (conjU u⁻¹ a : G) * a :=
      comm_of_br_eq_one (by unfold br; exact hc)
    have hk : uK a * uK (conjU u⁻¹ a) = uK (conjU u⁻¹ a) * uK a := Subtype.ext hc'
    rw [uK_conjU, inv_inv] at hk
    exact comm_form hk
  ·
    rw [← hσ₂]
    have hfix : vapp (h.act σ₂) (h.tv a) = h.tv a := by
      rw [hactσ₂', ha, Swap.vapp_mul, Swap.vapp_mul, hρfix _ (hp.1.1 n₁ hn₁),
        ← Swap.vapp_mul, hp.2.2.1, Swap.vapp_one]
    have hc := h.conjU_cube σ₂ (hR.pow_three hσ₂R') hfix
    have hk : uK a * σ₂ = σ₂ * uK a := by
      have := congrArg uK hc
      rw [uK_conjU] at this
      calc uK a * σ₂ = (σ₂ * uK a * σ₂⁻¹) * σ₂ := by rw [this]
        _ = σ₂ * uK a := by group
    exact comm_form hk
  ·
    rw [← hσ₂]
    exact comm_form (hR.comm hσR hσ₂R')
  ·
    rw [pow_two, pow_two, hv2, hA2]
  ·
    rw [pow_two]
    exact hu2
  ·
    rw [hui, hvi]
    calc u * (u * u') * u = (u * u) * u' * u := by group
      _ = u' * u := by rw [hu2, one_mul]

end CFSG.Quasithin.H13.U43
