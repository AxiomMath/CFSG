module

public import CFSG.Quasithin.H13.GoldschmidtU43CPair
public import CFSG.Quasithin.H13.GoldschmidtU43BK2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem zU_mul_zU : h.zU * h.zU = 1 := Subtype.ext h.sq_z

theorem zU_comm (x : ↥(Uz z)) : h.zU * x = x * h.zU := Subtype.ext (h.z_comm x.2)

theorem zU_ne_one : h.zU ≠ 1 := fun e => h.z_ne_one (congrArg Subtype.val e)

theorem conjU_zK (x : ↥(Uz z)) : conjU (zK z) x = x := by
  apply Subtype.ext
  rw [coe_conjU]
  show z * (x : G) * z⁻¹ = x
  calc z * (x : G) * z⁻¹ = ((x : G) * z) * z⁻¹ := by rw [h.z_comm x.2]
    _ = x := by group

theorem mul_self_of_q_one {a : ↥(Uz z)} (hq : q (h.tv a) = 1) : a * a = h.zU := by
  apply Subtype.ext
  have := h.sq_tv a
  rw [hq, zp_one, pow_two] at this
  exact this

theorem conjU_zU_mul (x : ↥(Hz z)) (u : ↥(Uz z)) : conjU x (h.zU * u) = h.zU * conjU x u := by
  rw [conjU_mul_right, h.conjU_zU]

theorem zU_mul_zU_mul (y : ↥(Uz z)) : h.zU * (h.zU * y) = y := by
  rw [← mul_assoc, h.zU_mul_zU, one_mul]

theorem zU_mul_mul_zU (u b : ↥(Uz z)) : (h.zU * u) * (h.zU * b) = u * b := by
  calc (h.zU * u) * (h.zU * b) = h.zU * (u * (h.zU * b)) := mul_assoc _ _ _
    _ = h.zU * ((u * h.zU) * b) := by rw [← mul_assoc u h.zU b]
    _ = h.zU * ((h.zU * u) * b) := by rw [← h.zU_comm u]
    _ = h.zU * (h.zU * (u * b)) := by rw [mul_assoc h.zU u b]
    _ = u * b := h.zU_mul_zU_mul _

theorem exists_sign (σ : ↥(Hz z)) (hσ3 : σ ^ 3 = 1) (n : V4)
    (hsum : n + vapp (h.act σ) n + vapp (h.act σ) (vapp (h.act σ) n) = 0) :
    ∃ a : ↥(Uz z), h.tv a = n ∧ conjU σ⁻¹ (conjU σ⁻¹ a) = a * conjU σ⁻¹ a := by
  obtain ⟨u₁, hu₁⟩ := h.tv_surj n
  have h3 : σ * (σ * σ) = 1 := by rw [← pow_three]; exact hσ3
  have hinv : σ⁻¹ = σ * σ := inv_eq_of_mul_eq_one_right h3
  have hg3 : ∀ x : V4, vapp (h.act σ) (vapp (h.act σ) (vapp (h.act σ) x)) = x := by
    intro x
    rw [← Swap.vapp_mul, ← Swap.vapp_mul, ← map_mul, ← map_mul, mul_assoc, h3, map_one,
      Swap.vapp_one]
  set b := conjU σ⁻¹ u₁ with hb
  have htb : h.tv b = vapp (h.act σ) (vapp (h.act σ) n) := by
    rw [hb, h.tv_conj, hinv, map_mul, Swap.vapp_mul, hu₁]
  have htb' : h.tv (conjU σ⁻¹ b) = vapp (h.act σ) n := by
    rw [h.tv_conj, hinv, map_mul, Swap.vapp_mul, htb]
    have := hg3 (vapp (h.act σ) n)
    rw [← this]
    simp only [hg3]
  have htp : h.tv (u₁ * b) = vapp (h.act σ) n := by
    rw [h.tv_mul, htb, hu₁]
    apply eq_of_add_eq_zero_V4
    rw [← hsum]
    abel
  have hpb : h.tv (conjU σ⁻¹ b) = h.tv (u₁ * b) := by rw [htb', htp]
  rcases h.eq_of_tv_eq' hpb with h1 | h1
  · exact ⟨u₁, hu₁, h1⟩
  · refine ⟨h.zU * u₁, by rw [h.tv_mul, h.tv_zU, zero_add, hu₁], ?_⟩
    have e1 : conjU σ⁻¹ (h.zU * u₁) = h.zU * b := h.conjU_zU_mul _ _
    rw [e1, h.conjU_zU_mul, h1, h.zU_mul_zU_mul, h.zU_mul_mul_zU]

theorem mul_zU_mul (a y : ↥(Uz z)) : a * (h.zU * y) = h.zU * (a * y) := by
  rw [← mul_assoc, ← h.zU_comm a, mul_assoc]

theorem conjU_refl (v : ↥(Hz z)) (hv2 : v * v = zK z) {a j : ↥(Uz z)} (hqa : q (h.tv a) = 1)
    (hva : vapp (h.act v) (h.tv a) = h.tv a)
    (hvj : vapp (h.act v) (h.tv j) = h.tv a + h.tv j) : conjU v a = a⁻¹ := by
  have hφ2 : ∀ x : ↥(Uz z), conjU v (conjU v x) = x := fun x => by
    rw [← conjU_mul_left, hv2, h.conjU_zK]
  have haa : a * a = h.zU := h.mul_self_of_q_one hqa
  have hainv : a⁻¹ = h.zU * a := by
    symm
    apply eq_inv_of_mul_eq_one_left
    calc h.zU * a * a = h.zU * (a * a) := mul_assoc _ _ _
      _ = h.zU * h.zU := by rw [haa]
      _ = 1 := h.zU_mul_zU
  have h1 : conjU v a = a ∨ conjU v a = h.zU * a :=
    h.eq_of_tv_eq' (by rw [h.tv_conj, hva])
  have h2 : conjU v j = a * j ∨ conjU v j = h.zU * (a * j) :=
    h.eq_of_tv_eq' (by rw [h.tv_conj, hvj, h.tv_mul])
  rcases h1 with h1 | h1
  · exfalso
    have key : conjU v (conjU v j) = h.zU * j := by
      rcases h2 with h2 | h2
      · rw [h2, conjU_mul_right, h1, h2, ← mul_assoc, haa]
      · rw [h2, h.conjU_zU_mul, conjU_mul_right, h1, h2, h.mul_zU_mul, h.zU_mul_zU_mul,
          ← mul_assoc, haa]
    rw [hφ2] at key
    apply h.zU_ne_one
    have := congrArg (fun y => y * j⁻¹) key
    simpa using this.symm
  · rw [h1, hainv]

theorem conjU_cube (σ : ↥(Hz z)) (hσ3 : σ ^ 3 = 1) {a : ↥(Uz z)}
    (hσa : vapp (h.act σ) (h.tv a) = h.tv a) : conjU σ a = a := by
  rcases h.eq_of_tv_eq' (show h.tv (conjU σ a) = h.tv a by rw [h.tv_conj, hσa]) with h1 | h1
  · exact h1
  · exfalso
    have h3 : σ * (σ * σ) = 1 := by rw [← pow_three]; exact hσ3
    have e2 : conjU σ (conjU σ a) = a := by
      rw [h1, h.conjU_zU_mul, h1, h.zU_mul_zU_mul]
    have e3 : conjU σ (conjU σ (conjU σ a)) = h.zU * a := by rw [e2, h1]
    rw [← conjU_mul_left σ σ a, ← conjU_mul_left σ (σ * σ) a, h3, conjU_one] at e3
    apply h.zU_ne_one
    have := congrArg (fun y => y * a⁻¹) e3
    simpa using this.symm

end Hyp

end CFSG.Quasithin.H13.U43
