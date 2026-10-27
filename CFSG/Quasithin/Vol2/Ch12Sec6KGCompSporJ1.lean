module

public import CFSG.Walter.Models
public import CFSG.Walter.J1Props.Aut
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompL3Small

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.QuasithinUnique CFSG.Walter.J1Props

theorem not_autConf_walterJ1 {ν : MulAut walterJ1}
    {Lb Pb : Subgroup (MulAut walterJ1)} (h : AutConf walterJ1 ν Lb Pb) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := walterJ1) 7 (by rw [J1_card]; norm_num)
  have hzp : IsPGroup 7 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P7, hP7⟩ := hzp.exists_le_sylow
  obtain ⟨x, hx2, hxinv⟩ := J2_inverted (p := 7) (by norm_num) P7
  have hxz : x * z * x⁻¹ = z⁻¹ := hxinv z (hP7 (Subgroup.mem_zpowers z))
  have hz2 : z⁻¹ ≠ z := fun hzz => by
    have h2 : z ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← hzz]; exact inv_mul_cancel z
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hz] at this
    norm_num at this
  have hZ : Subgroup.center walterJ1 = ⊥ := by
    have := J1_simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center walterJ1) with hc | hc
    · exact hc
    · exfalso
      have hxc : x ∈ Subgroup.center walterJ1 := by rw [hc]; trivial
      apply hz2
      rw [← hxz, (Subgroup.mem_center_iff.mp hxc z).symm, mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := J3_aut ν
  have hl : ∀ y, ν y = g⁻¹⁻¹ * y * g⁻¹ := fun y => by rw [hg, MulAut.conj_apply, inv_inv]
  obtain ⟨hl2, -⟩ := h.involution_of_inner hZ hl
  have hg2 : orderOf g = 2 := by rwa [orderOf_inv] at hl2
  obtain ⟨c, hc⟩ := isConj_iff.mp (J1_isConj_involutions hx2 hg2)
  have hy : ν (c * z * c⁻¹) = (c * z * c⁻¹)⁻¹ := by
    rw [hg, MulAut.conj_apply, ← hc]
    calc c * x * c⁻¹ * (c * z * c⁻¹) * (c * x * c⁻¹)⁻¹ = c * (x * z * x⁻¹) * c⁻¹ := by group
      _ = (c * z * c⁻¹)⁻¹ := by rw [hxz]; group
  have hyo : orderOf (c * z * c⁻¹) = 7 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  rcases h.inv _ (by rw [hyo]; decide) hy with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [hyo] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [hyo] at this
    norm_num at this

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_j1 (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) : False := by
  have := hQ.finite
  exact not_autConf_walterJ1 (h.autConf.map (e.trans CFSG.Walter.walterJ1EquivNative.symm))

end CFSG.Quasithin.H13.S126C
