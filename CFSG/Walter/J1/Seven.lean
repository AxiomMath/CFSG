module

public import CFSG.Walter.J1.HSeven
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem coprime_thirty_of {n : ℕ} (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) (h5 : ¬ 5 ∣ n) :
    Nat.Coprime n 30 := by
  have c2 : Nat.Coprime n 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_two).mpr h2))
  have c3 : Nat.Coprime n 3 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_three).mpr h3))
  have c5 : Nat.Coprime n 5 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
    (by norm_num)).mpr h5))
  have : (30 : ℕ) = 2 * 3 * 5 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right c2 c3) c5

theorem coprime_of_coprime_thirty {n : ℕ} (hn : Nat.Coprime n 30) : Nat.Coprime n 120 := by
  have : (120 : ℕ) = 30 * 4 := by norm_num
  rw [this]
  refine Nat.Coprime.mul_right hn ?_
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this]
  exact Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (by norm_num) hn)

include h in
theorem coprime_card_centralizer {x : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30) :
    Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G))) 30 := by
  have key : ∀ p : ℕ, (p = 2 ∨ p = 3 ∨ p = 5) →
      ¬ p ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    intro p hp hdvd
    have : Fact p.Prime := ⟨by rcases hp with rfl | rfl | rfl <;> norm_num⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hw' : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hw]
    apply hx1
    exact h.eq_one_of_coprime_of_commute hx (by rw [hw']; rcases hp with rfl | rfl | rfl <;>
      simp) (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm
  exact coprime_thirty_of (key 2 (Or.inl rfl)) (key 3 (Or.inr (Or.inl rfl)))
    (key 5 (Or.inr (Or.inr rfl)))

include h in
theorem inf_centralizer_eq_bot {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro z ⟨hzx, hzt⟩
  rw [Subgroup.mem_bot]
  have hc := coprime_of_coprime_thirty (h.coprime_card_centralizer hx1 hx)
  have h1 : orderOf z ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [← Subgroup.orderOf_mk z hzx]
    exact orderOf_dvd_natCard _
  have h2 : orderOf z ∣ 120 := by
    rw [← h.card_centralizer_involution ht, ← Subgroup.orderOf_mk z hzt]
    exact orderOf_dvd_natCard _
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1 h2)

include h in
theorem inv_of_mem_centralizer {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) :
    ∀ w ∈ Subgroup.centralizer ({x} : Set G), t * w * t⁻¹ = w⁻¹ := by
  have ht2 := (orderOf_eq_two_iff.mp ht).1
  have htN : t ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) :
      Set G) := by
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    have h1 : t * w * t⁻¹ * (t * x * t⁻¹) = t * x * t⁻¹ * (t * w * t⁻¹) := by
      calc t * w * t⁻¹ * (t * x * t⁻¹) = t * (w * x) * t⁻¹ := by group
        _ = t * (x * w) * t⁻¹ := by rw [hw]
        _ = t * x * t⁻¹ * (t * w * t⁻¹) := by group
    rw [htx] at h1
    calc t * w * t⁻¹ * x = x * (x⁻¹ * (t * w * t⁻¹)) * x := by group
      _ = x * (t * w * t⁻¹ * x⁻¹) * x := by rw [← h1]
      _ = x * (t * w * t⁻¹) := by group
  exact inv_of_inf_centralizer_eq_bot ht2 htN (h.inf_centralizer_eq_bot hx1 hx ht)

include h in
theorem commute_of_mem_centralizer {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {v w : G}
    (hv : v ∈ Subgroup.centralizer ({x} : Set G)) (hw : w ∈ Subgroup.centralizer ({x} : Set G)) :
    v * w = w * v := by
  have := le_centralizer_of_inv (h.inv_of_mem_centralizer hx1 hx ht htx) hv
  exact (Subgroup.mem_centralizer_iff.mp this w hw).symm

include h in
theorem centralizer_eq_of_mem {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {z : G}
    (hz : z ∈ Subgroup.centralizer ({x} : Set G)) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have hzc : Nat.Coprime (orderOf z) 30 := by
    have h1 : orderOf z ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [← Subgroup.orderOf_mk z hz]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left h1 (h.coprime_card_centralizer hx1 hx)
  have htz : t * z * t⁻¹ = z⁻¹ := h.inv_of_mem_centralizer hx1 hx ht htx z hz
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hz).symm
  apply le_antisymm
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.commute_of_mem_centralizer hz1 hzc ht htz hw hxz
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.commute_of_mem_centralizer hx1 hx ht htx hw hz

include h in
theorem inverting_eq {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) :
    {u : G | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} =
      (fun a => a * t) '' (Subgroup.centralizer ({x} : Set G) : Set G) := by
  have ht2 := (orderOf_eq_two_iff.mp ht).1
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hu, hux⟩
    refine ⟨u * t, ?_, by rw [mul_assoc, ht2, mul_one]⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * t * x * (u * t)⁻¹ = x := by
      rw [mul_inv_rev, show u * t * x * (t⁻¹ * u⁻¹) = u * (t * x * t⁻¹) * u⁻¹ by group, htx,
        show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group, hux, inv_inv]
    calc u * t * x = u * t * x * (u * t)⁻¹ * (u * t) := by group
      _ = x * (u * t) := by rw [h1]
  · rintro ⟨a, ha, rfl⟩
    have hta : t * a * t⁻¹ = a⁻¹ := h.inv_of_mem_centralizer hx1 hx ht htx a ha
    refine ⟨orderOf_eq_two_iff.mpr ⟨(mul_mul_self_eq_one_iff ht2).mpr hta, fun h1 => hx1 ?_⟩, ?_⟩
    · have htC : t ∈ Subgroup.centralizer ({x} : Set G) := by
        have : t = a⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact Subgroup.inv_mem _ ha
      have h2 : t * x * t⁻¹ = x := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp htC, mul_inv_cancel_right]
      rw [htx] at h2
      have h3 : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [h2]
          _ = 1 := mul_inv_cancel x
      have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
      have h5 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 30) hx) h4
      exact orderOf_eq_one_iff.mp h5
    · rw [mul_inv_rev, show a * t * x * (t⁻¹ * a⁻¹) = a * (t * x * t⁻¹) * a⁻¹ by group, htx]
      have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      calc a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hax, mul_inv_cancel_right]

include h in
theorem ncard_inverting_eq {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) :
    {u : G | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹}.ncard =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  rw [h.inverting_eq hx1 hx ht htx, Set.ncard_image_of_injective _ (mul_left_injective t)]
  exact (Nat.card_coe_set_eq _).symm

end JankoHyp

@[reducible, expose] def conjActionElems {G : Type*} [Group G] (K : Subgroup G) (S : Set G)
    (hS : ∀ k ∈ K, ∀ u ∈ S, k * u * k⁻¹ ∈ S) : MulAction K S where
  smul k u := ⟨k * u * (k : G)⁻¹, hS k k.2 u u.2⟩
  one_smul u := Subtype.ext (by
    change ((1 : K) : G) * u * ((1 : K) : G)⁻¹ = u
    simp)
  mul_smul k l u := Subtype.ext (by
    change ((k : G) * l) * u * ((k : G) * l)⁻¹ = k * (l * u * (l : G)⁻¹) * (k : G)⁻¹
    group)

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem ncard_inverting_commute {x t : G} (hx1 : x ≠ 1) (hx : Nat.Coprime (orderOf x) 30)
    (ht : orderOf t = 2) (htx : t * x * t⁻¹ = x⁻¹) {w : G} (hw : orderOf w = 3)
    (hwx : w * x * w⁻¹ ∈ Subgroup.zpowers x) :
    {u : G | (orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹) ∧ u * w = w * u}.ncard = 1 := by
  classical
  set S := {u : G | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹}
  set W := Subgroup.zpowers w
  have hwN : w ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    mem_normalizer_zpowers_iff.mpr hwx
  have hS : ∀ k ∈ W, ∀ u ∈ S, k * u * k⁻¹ ∈ S := by
    intro k hk u ⟨hu, hux⟩
    have hkN : k ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le).mpr hwN hk
    refine ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu], ?_⟩
    have hk' : k⁻¹ * x * k ∈ Subgroup.zpowers x := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) x).mp
        (Subgroup.mem_zpowers x)
      simpa using this
    obtain ⟨j, hj⟩ := hk'
    have hinv : u * (k⁻¹ * x * k) * u⁻¹ = (k⁻¹ * x * k)⁻¹ := by
      rw [← hj]
      change u * x ^ j * u⁻¹ = (x ^ j)⁻¹
      rw [← conj_zpow, hux, inv_zpow]
    calc k * u * k⁻¹ * x * (k * u * k⁻¹)⁻¹ = k * (u * (k⁻¹ * x * k) * u⁻¹) * k⁻¹ := by group
      _ = x⁻¹ := by rw [hinv]; group
  let := conjActionElems W S hS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  have : Finite S := Set.toFinite _ |>.to_subtype
  have hmod := hW3.card_modEq_card_fixedPoints S
  have hfix : Nat.card (MulAction.fixedPoints W S) =
      {u : G | (orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹) ∧ u * w = w * u}.ncard := by
    have hset : {u : G | (orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹) ∧ u * w = w * u} =
        (fun u : S => (u : G)) '' (MulAction.fixedPoints W S) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hu, huw⟩
        refine ⟨⟨u, hu⟩, ?_, rfl⟩
        rintro ⟨k, j, rfl⟩
        apply Subtype.ext
        change w ^ j * u * (w ^ j)⁻¹ = u
        rw [(Commute.zpow_left (Commute.symm huw) j).eq, mul_inv_cancel_right]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v.2, ?_⟩
        have := congrArg Subtype.val (hv ⟨w, Subgroup.mem_zpowers w⟩)
        change w * v * w⁻¹ = v at this
        calc (v : G) * w = w * v * w⁻¹ * w := by rw [this]
          _ = w * v := by group
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]
  rw [hfix, Nat.card_coe_set_eq, h.ncard_inverting_eq hx1 hx ht htx] at hmod
  have hle : {u : G | (orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹) ∧ u * w = w * u}.ncard ≤ 1 := by
    rw [Set.ncard_le_one (Set.toFinite _)]
    rintro u ⟨⟨hu, hux⟩, huw⟩ v ⟨⟨hv, hvx⟩, hvw⟩
    by_contra huv
    have hu2 := (orderOf_eq_two_iff.mp hu).1
    have hv2 := (orderOf_eq_two_iff.mp hv).1
    have hz : u * v ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : u * v * x * (u * v)⁻¹ = x := by
        rw [mul_inv_rev, show u * v * x * (v⁻¹ * u⁻¹) = u * (v * x * v⁻¹) * u⁻¹ by group, hvx,
          show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group, hux, inv_inv]
      calc u * v * x = u * v * x * (u * v)⁻¹ * (u * v) := by group
        _ = x * (u * v) := by rw [h1]
    have hz1 : u * v ≠ 1 := by
      intro h1
      apply huv
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, inv_eq_of_mul_eq_one_right hv2]
    have hwz : w ∈ Subgroup.centralizer ({u * v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * (u * v) = u * w * v := by rw [← mul_assoc, ← huw]
        _ = u * v * w := by rw [mul_assoc, ← hvw, ← mul_assoc]
    rw [h.centralizer_eq_of_mem hx1 hx ht htx hz hz1] at hwz
    have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [← hw, ← Subgroup.orderOf_mk w hwz]
      exact orderOf_dvd_natCard _
    have hc := h.coprime_card_centralizer hx1 hx
    have : Nat.gcd (Nat.card (Subgroup.centralizer ({x} : Set G))) 30 ≠ 1 := by
      intro h1
      have := Nat.dvd_gcd h3 (by norm_num : 3 ∣ 30)
      rw [h1] at this
      norm_num at this
    exact this hc
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    intro h3
    have hc := h.coprime_card_centralizer hx1 hx
    have := Nat.dvd_gcd h3 (by norm_num : 3 ∣ 30)
    rw [hc] at this
    norm_num at this
  unfold Nat.ModEq at hmod
  omega

end JankoHyp

end CFSG.Walter.J1
