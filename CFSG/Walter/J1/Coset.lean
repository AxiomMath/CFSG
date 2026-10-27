module

public import CFSG.Walter.J1.HSeven

public section

namespace CFSG.Walter.J1

@[expose] def cosetD {G : Type*} [Group G] (H : Subgroup G) (u : G) : Subgroup G :=
  H ⊓ H.map (MulAut.conj u⁻¹).toMonoidHom

theorem mem_cosetD {G : Type*} [Group G] {H : Subgroup G} {u d : G} :
    d ∈ cosetD H u ↔ d ∈ H ∧ u * d * u⁻¹ ∈ H := by
  unfold cosetD
  rw [Subgroup.mem_inf, mem_map_conj, inv_inv]

theorem card_mul_card_le_of_inf_eq_bot {G : Type*} [Group G] {D X Y : Subgroup G} [Finite D]
    (hX : X ≤ D) (hY : Y ≤ D) (hXY : X ⊓ Y = ⊥) : Nat.card X * Nat.card Y ≤ Nat.card D := by
  let φ : X × Y → D := fun p => ⟨p.1 * p.2, D.mul_mem (hX p.1.2) (hY p.2.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ X ⊓ Y :=
      ⟨X.mul_mem (X.inv_mem a'.2) a.2, h2 ▸ Y.mul_mem b'.2 (Y.inv_mem b.2)⟩
    rw [hXY, Subgroup.mem_bot] at h3
    have h4 : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    rw [h4] at h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext (mul_left_cancel h1))
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod] at this

theorem zpowers_inf_eq_bot {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {y z : G}
    (hz : orderOf z = p) (hzy : z ∉ Subgroup.zpowers y) :
    Subgroup.zpowers y ⊓ Subgroup.zpowers z = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwy, hwz⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  apply hzy
  have hZ : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have heq := eq_zpowers_of_card_prime hp hZ hwz hw1
  have : z ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers z
  exact (Subgroup.zpowers_le).mpr hwy this

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem eq_of_mem_cosetD (Q : Sylow 2 G) {u : G}
    (huH : u ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G)) {s s' : G}
    (hs : s ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u)
    (hs' : s' ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u)
    (hs2 : orderOf s = 2) (hs'2 : orderOf s' = 2) : s = s' := by
  rw [mem_cosetD] at hs hs'
  have hsQ := mem_sylow_of_orderOf_eq_two Q hs.1 hs2
  have hs'Q := mem_sylow_of_orderOf_eq_two Q hs'.1 hs'2
  have hus : u * s * u⁻¹ ∈ Q := mem_sylow_of_orderOf_eq_two Q hs.2
    (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs2])
  have hus' : u * s' * u⁻¹ ∈ Q := mem_sylow_of_orderOf_eq_two Q hs'.2
    (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs'2])
  by_contra hne
  have hQab := h.abelian_sylow Q
  have hcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q := fun q hq r hr =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨q, hq⟩ ⟨r, hr⟩)
  apply huH
  have hconj : ∀ q ∈ (Q : Subgroup G), u⁻¹ * q * u⁻¹⁻¹ ∈ (Q : Subgroup G) := by
    intro q hq
    rw [inv_inv]
    have key : ∀ v : G, u * v * u⁻¹ ∈ Q → u⁻¹ * q * u * v = v * (u⁻¹ * q * u) := by
      intro v hv
      have := hcomm q hq _ hv
      calc u⁻¹ * q * u * v = u⁻¹ * (q * (u * v * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * v * u⁻¹) * q) * u := by rw [this]
        _ = v * (u⁻¹ * q * u) := by group
    exact h.mem_sylow_of_commute_four Q hsQ hs'Q (orderOf_eq_two_iff.mp hs2).2
      (orderOf_eq_two_iff.mp hs'2).2 hne (key s hus) (key s' hus')
  exact inv_mem_iff.mp (mem_normalizer_of_conj_mem hconj)

theorem conj_mem_cosetD {G : Type*} [Group G] {H : Subgroup G} {u d : G} (hu : u * u = 1)
    (hd : d ∈ cosetD H u) : u * d * u⁻¹ ∈ cosetD H u := by
  rw [mem_cosetD] at hd ⊢
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  refine ⟨hd.2, ?_⟩
  rw [huinv] at hd ⊢
  rw [show u * (u * d * u) * u = (u * u) * d * (u * u) by group, hu, one_mul, mul_one]
  exact hd.1

include h in
theorem card_cosetD_dvd (Q : Sylow 2 G) (u : G) :
    Nat.card (cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u) ∣ 168 := by
  rw [← h.card_normalizer_sylow'' Q]
  exact Subgroup.card_dvd_of_le inf_le_left

include h in
theorem card_cosetD_dvd_21 (Q : Sylow 2 G) (u : G)
    (h2 : ∀ s ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u, orderOf s ≠ 2) :
    Nat.card (cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u) ∣ 21 := by
  set D := cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u
  have hodd : ¬ 2 ∣ Nat.card D := by
    intro h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h0
    exact h2 s s.2 (by rw [Subgroup.orderOf_coe, hs])
  have h168 : Nat.card D ∣ 168 := h.card_cosetD_dvd Q u
  have hc : Nat.Coprime (Nat.card D) 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr hodd)))
  rw [show (168 : ℕ) = 8 * 21 by norm_num] at h168
  exact hc.dvd_of_dvd_mul_left h168

include h in
theorem card_cosetD_dvd_6 (Q : Sylow 2 G) {u : G}
    (huH : u ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (h7 : ∀ y ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u, orderOf y ≠ 7) :
    Nat.card (cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u) ∣ 6 := by
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  set D := cosetD H u
  have h7' : ¬ 7 ∣ Nat.card D := by
    intro h0
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h0
    exact h7 y y.2 (by rw [Subgroup.orderOf_coe, hy])
  have h4 : ¬ 4 ∣ Nat.card D := by
    intro h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 2 (n := 2)
      (by simpa using h0)
    have hK' : Nat.card (K.map D.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective D.subtype_injective, hK]
      norm_num
    obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_of_card_four hK'
    have hKD : K.map D.subtype ≤ D := Subgroup.map_subtype_le K
    have hsq : ∀ c ∈ K.map D.subtype, c ≠ 1 → orderOf c = 2 := by
      intro c hc hc1
      have hc4 : c ^ 2 ^ 2 = 1 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hK']
        exact pow_card_eq_one_of_mem hc
      have hcQ := mem_sylow_of_mem_normalizer Q ((mem_cosetD.mp (hKD hc)).1) hc4
      exact orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q hcQ, hc1⟩
    exact hab (h.eq_of_mem_cosetD Q huH (hKD ha) (hKD hb) (hsq a ha ha1) (hsq b hb hb1))
  have h168 : Nat.card D ∣ 168 := h.card_cosetD_dvd Q u
  have hmem : Nat.card D ∈ Nat.divisors 168 := Nat.mem_divisors.mpr ⟨h168, by norm_num⟩
  have : Nat.divisors 168 = {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by
    decide
  rw [this] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 |
    h0 <;> rw [h0] at h7' h4 ⊢ <;> omega

section Seven

variable (Q : Sylow 2 G) {u : G} (hu : orderOf u = 2)
  (huH : u ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G)) {y : G}
  (hyD : y ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u) (hy : orderOf y = 7)

include h huH hyD hy in
theorem orderOf_ne_two_of_seven :
    ∀ s ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u, orderOf s ≠ 2 := by
  intro s hs hs2
  set D := cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u
  have hys : y * s * y⁻¹ ∈ D := D.mul_mem (D.mul_mem hyD hs) (D.inv_mem hyD)
  have h1 := h.eq_of_mem_cosetD Q huH hys hs
    (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs2]) hs2
  have h2 : y * s = s * y := by
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h1]
  have := h.eq_one_of_coprime_of_commute (x := s) (y := y) (by rw [hy]; norm_num)
    (Or.inl hs2) h2
  rw [this, orderOf_one] at hy
  omega

include h huH hyD hy in
theorem mem_zpowers_of_seven {z : G}
    (hzD : z ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u)
    (hz : orderOf z = 7) : z ∈ Subgroup.zpowers y := by
  set D := cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u
  by_contra hzy
  have h21 : Nat.card D ∣ 21 := h.card_cosetD_dvd_21 Q u (h.orderOf_ne_two_of_seven Q huH hyD hy)
  have hle := card_mul_card_le_of_inf_eq_bot (D := D) ((Subgroup.zpowers_le).mpr hyD)
    ((Subgroup.zpowers_le).mpr hzD) (zpowers_inf_eq_bot (by norm_num) hz hzy)
  rw [Nat.card_zpowers, Nat.card_zpowers, hy, hz] at hle
  have := Nat.le_of_dvd (by norm_num) h21
  omega

include h hu huH hyD hy in
theorem inv_of_seven : ∀ z ∈ Subgroup.zpowers y, u * z * u⁻¹ = z⁻¹ := by
  have hu2 := (orderOf_eq_two_iff.mp hu).1
  have huy := conj_mem_cosetD hu2 hyD
  have huy7 : orderOf (u * y * u⁻¹) = 7 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have huN : u ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    mem_normalizer_zpowers_iff.mpr (h.mem_zpowers_of_seven Q huH hyD hy huy huy7)
  refine inv_of_inf_centralizer_eq_bot hu2 huN ?_
  rw [eq_bot_iff]
  rintro w ⟨hwy, hwu⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hZ : Nat.card (Subgroup.zpowers y) = 7 := by rw [Nat.card_zpowers, hy]
  have heq := eq_zpowers_of_card_prime (by norm_num) hZ hwy hw1
  have hyw : y ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := hyw
  have hyu : y * u = u * y := by
    rw [← hk]
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hwu) k).eq
  have := h.eq_one_of_coprime_of_commute (x := u) (y := y) (by rw [hy]; norm_num)
    (Or.inl hu) hyu
  rw [this, orderOf_one] at hy
  omega

include h hu huH hyD hy in
theorem inv_set_eq_of_seven :
    {d | d ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ u * d * u⁻¹ = d⁻¹} =
      (Subgroup.zpowers y : Set G) := by
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  set D := cosetD H u
  have hinv := h.inv_of_seven Q hu huH hyD hy
  ext d
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hdH, hdu⟩
    have hdD : d ∈ D := mem_cosetD.mpr ⟨hdH, hdu ▸ H.inv_mem hdH⟩
    rcases h.orderOf_mem_normalizer Q hdH with h0 | h0 | h0 | h0 | h0
    · rw [orderOf_eq_one_iff.mp h0]
      exact Subgroup.one_mem _
    · exact absurd h0 (h.orderOf_ne_two_of_seven Q huH hyD hy d hdD)
    · exfalso
      have hdy : d * y * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hdD hyD) (D.inv_mem hdD)
      have hdy7 : orderOf (d * y * d⁻¹) = 7 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
      have h1 := hinv _ (h.mem_zpowers_of_seven Q huH hyD hy hdy hdy7)
      have hyinv := hinv y (Subgroup.mem_zpowers y)
      have hdinv : u * d⁻¹ * u⁻¹ = d := by
        rw [show u * d⁻¹ * u⁻¹ = (u * d * u⁻¹)⁻¹ by group, hdu, inv_inv]
      have h2 : d⁻¹ * y⁻¹ * d = d * y⁻¹ * d⁻¹ := by
        calc d⁻¹ * y⁻¹ * d = (u * d * u⁻¹) * (u * y * u⁻¹) * (u * d⁻¹ * u⁻¹) := by
              rw [hdu, hyinv, hdinv]
          _ = u * (d * y * d⁻¹) * u⁻¹ := by group
          _ = (d * y * d⁻¹)⁻¹ := h1
          _ = d * y⁻¹ * d⁻¹ := by group
      have hd3 : d ^ 3 = 1 := by rw [← h0]; exact pow_orderOf_eq_one d
      have h3 : d * d * y⁻¹ = y⁻¹ * (d * d) := by
        calc d * d * y⁻¹ = d * (d * y⁻¹ * d⁻¹) * d := by group
          _ = d * (d⁻¹ * y⁻¹ * d) * d := by rw [h2]
          _ = y⁻¹ * (d * d) := by group
      have h4 : (d * d) * y = y * (d * d) := by
        calc d * d * y = y * (y⁻¹ * (d * d)) * y := by group
          _ = y * (d * d * y⁻¹) * y := by rw [h3]
          _ = y * (d * d) := by group
      have hdd : (d * d) * (d * d) = d := by
        have : (d * d) * (d * d) = d ^ 3 * d := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [this, hd3, one_mul]
      have h5 : d * y = y * d := by
        calc d * y = (d * d) * (d * d) * y := by rw [hdd]
          _ = y * ((d * d) * (d * d)) := by
              rw [mul_assoc, h4, ← mul_assoc, h4, mul_assoc]
          _ = y * d := by rw [hdd]
      have := h.eq_one_of_coprime_of_commute (x := d) (y := y) (by rw [hy]; norm_num)
        (Or.inr (Or.inl h0)) h5.symm
      rw [this, orderOf_one] at hy
      omega
    · exfalso
      have hs : orderOf (d ^ 3) = 2 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [h0]; norm_num), h0]
      exact h.orderOf_ne_two_of_seven Q huH hyD hy (d ^ 3) (D.pow_mem hdD 3) hs
    · exact h.mem_zpowers_of_seven Q huH hyD hy hdD h0
  · intro hd
    refine ⟨?_, hinv d hd⟩
    exact (Subgroup.zpowers_le).mpr (mem_cosetD.mp hyD).1 hd

include h huH hyD hy in
theorem conj_mem_zpowers_of_seven {x : G}
    (hxD : x ∈ cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u) :
    x * y * x⁻¹ ∈ Subgroup.zpowers y := by
  set D := cosetD (Subgroup.normalizer ((Q : Subgroup G) : Set G)) u
  exact h.mem_zpowers_of_seven Q huH hyD hy (D.mul_mem (D.mul_mem hxD hyD) (D.inv_mem hxD))
    (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy])

end Seven

end JankoHyp

end CFSG.Walter.J1
