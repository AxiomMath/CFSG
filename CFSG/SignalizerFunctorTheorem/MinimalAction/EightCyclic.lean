module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.EightSubgroup

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

namespace EightSetting

variable {P : Subgroup G} {d : G} {W : Subgroup G}

omit [Finite G] in
private theorem commute_of_mem_zpowers {a b x : G} (hab : a * b = b * a)
    (hx : x ∈ Subgroup.zpowers a) : x * b = b * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact (Commute.zpow_left (show Commute a b from hab) k).eq

private theorem card_eq_three_of_cyclic (h : EightSetting P d W) (D : Sylow 3 G)
    (hdD : d ∈ (D : Subgroup G)) (hcyc : IsCyclic (D : Subgroup G)) :
    Nat.card (D : Subgroup G) = 3 := by
  obtain ⟨y, hy⟩ := hcyc.exists_generator
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hy ⟨d, hdD⟩)
  have hdy : (y : G) ^ k = d := by simpa using congrArg Subtype.val hk
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.ne_bot
  have hyw : (y : G) * w ≠ w * y := by
    intro hyc
    have hd : d * w = w * d := commute_of_mem_zpowers hyc (Subgroup.mem_zpowers_iff.2 ⟨k, hdy⟩)
    exact hw1 (Subtype.ext (h.free w hwW (by rw [hd, mul_inv_cancel_right])))
  have hyG : IsPGroup 3 (Subgroup.zpowers (y : G)) :=
    D.isPGroup'.to_le (Subgroup.zpowers_le.2 y.2)
  have hy3 : (y : G) ^ 3 = 1 := (h.star hyG ⟨w, hwW, hyw⟩).2.2
  have hdvd : Nat.card (D : Subgroup G) ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hy]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy3))
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exfalso
    have hbot : (D : Subgroup G) = ⊥ := (Subgroup.eq_bot_iff_card (H := (D : Subgroup G))).2 h1
    apply h.ne_one
    have hd1 : d ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hdD
    exact Subgroup.mem_bot.1 hd1
  · exact h3

private theorem exists_conj_commute (D : Sylow 3 G) (hdD : d ∈ (D : Subgroup G))
    (hD : Nat.card (D : Subgroup G) = 3) {u t : G} (hu : orderOf u = 3)
    (htu : t * u = u * t) : ∃ c : G, c * t * c⁻¹ * d = d * (c * t * c⁻¹) := by
  have hup : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨D', hD'⟩ := hup.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G D' D
  have hv : c * u * c⁻¹ ∈ (D : Subgroup G) := by
    have h2 : c * u * c⁻¹ ∈ ((c • D' : Sylow 3 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨u, hD' (Subgroup.mem_zpowers u), by simp [MulAut.conj_apply]⟩
    rwa [hc] at h2
  have hv1 : c * u * c⁻¹ ≠ 1 := by
    rw [Ne, conj_eq_one_iff]
    rintro rfl
    simp at hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card (p := 3) hD (g := (⟨c * u * c⁻¹, hv⟩ : (D : Subgroup G)))
      (g' := ⟨d, hdD⟩) (fun h1 => hv1 (congrArg Subtype.val h1)))
  have hdk : (c * u * c⁻¹) ^ k = d := by simpa using congrArg Subtype.val hk
  have hcomm : c * u * c⁻¹ * (c * t * c⁻¹) = c * t * c⁻¹ * (c * u * c⁻¹) := by
    calc c * u * c⁻¹ * (c * t * c⁻¹) = c * (u * t) * c⁻¹ := by group
      _ = c * (t * u) * c⁻¹ := by rw [htu]
      _ = c * t * c⁻¹ * (c * u * c⁻¹) := by group
  exact ⟨c, (commute_of_mem_zpowers hcomm (Subgroup.mem_zpowers_iff.2 ⟨k, hdk⟩)).symm⟩

private theorem false_of_involution (h : EightSetting P d W) {t : G} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (htd : t * d = d * t) : False := by
  have hWn : W.Normal := h.normal_left
  have hW4 := h.card_eq_four
  have hp2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hWn]
    exact le_top
  have hmod := centralizer_card_modEq 2 Nat.prime_two (Subgroup.zpowers t) W hp2 hnorm
  generalize hC : W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) = C at hmod
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ W ∧ t * x = x * t := by
    intro x
    rw [← hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨fun hx => ⟨hx.1, hx.2 t (Subgroup.mem_zpowers t)⟩,
      fun hx => ⟨hx.1, fun s hs => commute_of_mem_zpowers hx.2 hs⟩⟩
  have hCW : C ≤ W := fun x hx => ((hmemC x).1 hx).1
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle : Nat.card C ≤ 4 := by
    have hdvd := Subgroup.card_dvd_of_le hCW
    rw [hW4] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hmod' : Nat.card W % 2 = Nat.card C % 2 := hmod
  have hCW' : C = W := by
    rcases (by omega : Nat.card C = 2 ∨ Nat.card C = 4) with h2 | h4
    · exfalso
      obtain ⟨⟨x, hxC⟩, hx1, huniq⟩ := (Nat.card_eq_two_iff' (1 : C)).1 h2
      obtain ⟨hxW, hxt⟩ := (hmemC x).1 hxC
      have hdxC : d * x * d⁻¹ ∈ C := by
        rw [hmemC]
        have hcd : Commute t d := htd
        have hcx : Commute t x := hxt
        exact ⟨(Subgroup.mem_set_normalizer_iff.1 h.normalizes x).1 hxW,
          ((hcd.mul_right hcx).mul_right hcd.inv_right).eq⟩
      have hne : (⟨d * x * d⁻¹, hdxC⟩ : C) ≠ 1 := by
        intro h1
        have h1' : d * x * d⁻¹ = 1 := congrArg Subtype.val h1
        exact hx1 (Subtype.ext (conj_eq_one_iff.1 h1'))
      have hxeq : d * x * d⁻¹ = x := congrArg Subtype.val (huniq _ hne)
      exact hx1 (Subtype.ext (h.free x hxW hxeq))
    · exact Subgroup.eq_of_le_of_card_ge hCW (by omega)
  have hcent : ∀ w ∈ W, t * w = w * t := fun w hw =>
    ((hmemC w).1 (by rw [hCW']; exact hw)).2
  have htW : t ∉ W := fun htW =>
    ht1 (h.free t htW (by rw [← htd, mul_inv_cancel_right]))
  have hE : IsElemAbelian 2 (W ⊔ Subgroup.zpowers t) :=
    isElemAbelian_sup h.elem (isElemAbelian_zpowers ht2) fun a ha b hb =>
      (commute_of_mem_zpowers (hcent a ha) hb).symm
  have hlt : W < W ⊔ Subgroup.zpowers t := by
    refine lt_of_le_of_ne le_sup_left fun heq => htW ?_
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have h1 := CFSG.natCard_lt_of_subgroup_lt hlt
  have h2 := h.rank _ hE
  omega

theorem cyclic_case (h : EightSetting P d W) (hsix : ∃ x : G, orderOf x = 6) (D : Sylow 3 G)
    (hdD : d ∈ (D : Subgroup G)) (hcyc : IsCyclic (D : Subgroup G)) : False := by
  obtain ⟨g, hg⟩ := hsix
  have hu : orderOf (g ^ 2) = 3 := by
    have hord := orderOf_pow_of_dvd (x := g) (n := 2) (by norm_num) (by rw [hg]; norm_num)
    rw [hg] at hord
    omega
  have ht : orderOf (g ^ 3) = 2 := by
    have hord := orderOf_pow_of_dvd (x := g) (n := 3) (by norm_num) (by rw [hg]; norm_num)
    rw [hg] at hord
    omega
  have ht1 : g ^ 3 ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    omega
  have ht2 : (g ^ 3) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (g ^ 3)
    rwa [ht] at this
  obtain ⟨c, hc⟩ := exists_conj_commute D hdD (h.card_eq_three_of_cyclic D hdD hcyc) hu
    ((Commute.refl g).pow_pow 3 2).eq
  refine h.false_of_involution (t := c * g ^ 3 * c⁻¹) ?_ ?_ hc
  · rw [conj_pow, ht2]
    simp
  · exact fun h1 => ht1 (conj_eq_one_iff.1 h1)

end EightSetting

end CFSG.SignalizerFunctorTheorem.MinimalAction
