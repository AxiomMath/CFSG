module

public import CFSG.Walter.J1Recog.Setup

public section

namespace CFSG.Walter.J1Recog

open CFSG.Walter.J1

namespace Setup

variable {G : Type} [Group G] [Finite G] (X : Setup G)

include X in
theorem counts :
    (∀ Y : Subgroup G, Nat.card Y = 3 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (Y : Set G)}.ncard = 5) ∧
    (∀ P : Subgroup G, Nat.card P = 5 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (P : Set G)}.ncard = 3) ∧
    {u : G | orderOf u = 2 ∧ u * X.n * u⁻¹ = X.n⁻¹}.ncard ≠ 0 := by
  obtain ⟨d, hd13, hd3, hd5⟩ := X.h.exists_d
  obtain ⟨b0, b1, b2, b3, b6, b7, c, k, hJ, hI, hb2, hb6, hb3, hb7, hc, hk⟩ :=
    X.h.count_relations X.S hd3 X.n_mem X.orderOf_n
  have hG120 := X.h.ncard_involutions_mul
  have hG168 : 168 * (Subgroup.normalizer ((X.S : Subgroup G) : Set G)).index = Nat.card G := by
    rw [← X.h.card_normalizer_sylow'' X.S]
    exact Subgroup.card_mul_index _
  rw [X.card_G] at hG120 hG168
  set r := {u : G | orderOf u = 2 ∧ u * X.n * u⁻¹ = X.n⁻¹}.ncard
  have hd : d = 3 ∧ r ≠ 0 := by
    by_cases hr : r = 0
    · simp only [hr, ↓reduceIte] at hc
      rw [hr] at hb7
      exfalso
      rcases hd13 with rfl | rfl <;> omega
    · simp only [hr, ↓reduceIte] at hc
      refine ⟨?_, hr⟩
      rcases hd13 with rfl | rfl <;> omega
  obtain ⟨rfl, hr⟩ := hd
  exact ⟨fun Y hY => (hd3 Y hY).1, hd5, hr⟩

include X in
theorem card_centralizer {p : ℕ} (hp : p = 3 ∨ p = 5) {Y : Subgroup G} (hY : Nat.card Y = p) :
    Nat.card (Subgroup.centralizer (Y : Set G)) = 30 := by
  have h := X.h.ncard_centralizing_mul hp hY
  rcases hp with rfl | rfl
  · rw [(X.counts).1 Y hY] at h; omega
  · rw [(X.counts).2.1 Y hY] at h; omega

include X in
theorem exists_A {p : ℕ} (hp : p = 3 ∨ p = 5) {Y : Subgroup G} (hY : Nat.card Y = p) {x : G}
    (hx : orderOf x = 2) (hYx : Y ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer (Y : Set G) ∧ Y ≤ A ∧
      A ⊓ Subgroup.centralizer ({x} : Set G) = Y ∧ Nat.card A = 15 ∧
      (∀ y ∈ Subgroup.centralizer (Y : Set G), Odd (orderOf y) → y ∈ A) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (A.subgroupOf (Subgroup.centralizer (Y : Set G))).index = 2 := by
  obtain ⟨-, A, -, -, -, hAC, hYA, hAx, hA2, hodd, habel, -⟩ :=
    X.h.bender_4_1_of_centralizer hp hY hx hYx
  have h30 := X.card_centralizer hp hY
  have hA : Nat.card A = 15 := by omega
  refine ⟨A, hAC, hYA, hAx, hA, hodd, habel, ?_⟩
  have h1 := (A.subgroupOf (Subgroup.centralizer (Y : Set G))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA, h30] at h1
  omega

omit [Finite G] in
theorem mul_mem_of_index_two {C A : Subgroup G} (hA : (A.subgroupOf C).index = 2) {a b : G}
    (ha : a ∈ C) (hb : b ∈ C) (haA : a ∉ A) (hbA : b ∉ A) : a * b ∈ A := by
  have := (Subgroup.mul_mem_iff_of_index_two hA (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    (iff_of_false (by simpa [Subgroup.mem_subgroupOf] using haA)
      (by simpa [Subgroup.mem_subgroupOf] using hbA))
  simpa [Subgroup.mem_subgroupOf] using this

omit [Finite G] in
theorem not_mem_of_two {A : Subgroup G} (hA : Nat.card A = 15) {a : G} (ha : orderOf a = 2) :
    a ∉ A := by
  intro haA
  have := Subgroup.orderOf_dvd_natCard A haA
  rw [ha, hA] at this
  omega

theorem m_n_conj : X.m * X.n * X.m⁻¹ = X.n ^ 4 := by
  set z := X.m * X.n * X.m⁻¹
  have hz2 : z ^ 2 = X.n := by
    rw [conj_pow, ← X.m_n]
    group
  have hz7 : z ^ 7 = 1 := by rw [conj_pow, X.n_pow_seven]; group
  calc z = z ^ 8 := by rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, hz7, one_mul]
    _ = (z ^ 2) ^ 4 := by rw [← pow_mul]
    _ = X.n ^ 4 := by rw [hz2]

theorem exists_s : ∃ s : G, orderOf s = 2 ∧ s * X.n * s⁻¹ = X.n⁻¹ ∧ s * X.m = X.m * s := by
  obtain ⟨v, hv, hvn⟩ := Set.nonempty_of_ncard_ne_zero X.counts.2.2
  have h1 := X.h.ncard_inverting_commute (x := X.n) (t := v) X.n_ne_one
    (by rw [X.orderOf_n]; norm_num) hv hvn X.orderOf_m
    (by rw [X.m_n_conj]; exact Subgroup.npow_mem_zpowers _ _)
  obtain ⟨s, ⟨hs, hsn⟩, hsm⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h1]; norm_num)
  exact ⟨s, hs, hsn, hsm⟩

theorem t_mem_centralizer_m :
    X.t ∈ Subgroup.centralizer ((Subgroup.zpowers X.m : Subgroup G) : Set G) :=
  (mem_centralizer_zpowers_iff' _ _).mpr X.m_t.symm

theorem zpowers_m_le : Subgroup.zpowers X.m ≤ Subgroup.centralizer ({X.t} : Set G) :=
  Subgroup.zpowers_le.mpr X.m_mem_centralizer

theorem card_zpowers_m : Nat.card (Subgroup.zpowers X.m) = 3 := by
  rw [Nat.card_zpowers, X.orderOf_m]

theorem pow_five {x : G} (hx : orderOf x = 2) (hxm : x * X.m = X.m * x) (hxt : x ≠ X.t) :
    (X.t * x) ^ 5 = 1 ∧ X.t * x ≠ 1 := by
  obtain ⟨A, hAC, hUA, -, hA, -, habel, hidx⟩ := X.exists_A (Or.inl rfl) X.card_zpowers_m
    X.h.orderOf_t X.zpowers_m_le
  have hxC : x ∈ Subgroup.centralizer ((Subgroup.zpowers X.m : Subgroup G) : Set G) :=
    (mem_centralizer_zpowers_iff' _ _).mpr hxm
  have htx : X.t * x ∈ A := mul_mem_of_index_two hidx X.t_mem_centralizer_m hxC
    (not_mem_of_two hA X.h.orderOf_t) (not_mem_of_two hA hx)
  have hx2 : x * x = 1 := (orderOf_eq_two_iff.mp hx).1
  have h15 : (X.t * x) ^ 15 = 1 := by
    have := Subgroup.orderOf_dvd_natCard A htx
    rw [hA] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  set y := (X.t * x) ^ 5
  have hyA : y ∈ A := A.pow_mem htx 5
  have hy3 : y ^ 3 = 1 := by rw [← pow_mul]; exact h15
  have hty : X.t * y * X.t⁻¹ = y⁻¹ := by
    have hinv : X.t * (X.t * x) * X.t⁻¹ = (X.t * x)⁻¹ := by
      rw [mul_inv_rev, X.h.t_inv, inv_eq_of_mul_eq_one_right hx2, ← mul_assoc, X.t_mul_t,
        one_mul]
    show X.t * (X.t * x) ^ 5 * X.t⁻¹ = ((X.t * x) ^ 5)⁻¹
    rw [← conj_pow, hinv, inv_pow]
  have hm1 : X.m ^ 3 = 1 := X.m_pow_three
  have hymem : y ∈ Subgroup.zpowers X.m := by
    by_cases hy1 : y = 1
    · rw [hy1]; exact Subgroup.one_mem _
    have := mem_zpowers_of_comm habel Nat.prime_three (by rw [hA]; norm_num) hyA
      (hUA (Subgroup.mem_zpowers X.m)) hy3 hm1 X.m_ne_one
    exact this
  have hyt : y * X.t = X.t * y := by
    obtain ⟨k, hk⟩ := hymem
    rw [← hk]
    exact (Commute.zpow_left (show Commute X.m X.t from X.m_t) k).eq
  have hy1 : y = 1 := by
    have hyy : y = y⁻¹ := by
      rw [← hty, ← hyt, mul_assoc, mul_inv_cancel, mul_one]
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [hyy]; exact mul_inv_cancel y
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy3, hy2, inv_one, one_mul]
  refine ⟨hy1, fun h1 => hxt ?_⟩
  calc x = X.t * (X.t * x) := by rw [← mul_assoc, X.t_mul_t, one_mul]
    _ = X.t := by rw [h1, mul_one]

omit [Finite G] in
theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem exists_u {s : G} (hs : orderOf s = 2) (hsm : s * X.m = X.m * s) (hst : s ≠ X.t) :
    ∃ u : G, orderOf u = 2 ∧ u * X.t = X.t * u ∧ u * s = s * u ∧ u * X.m * u⁻¹ = X.m⁻¹ := by
  have hm15 : X.m ^ 15 = 1 := by
    rw [show (15 : ℕ) = 3 * 5 from rfl, pow_mul, X.m_pow_three, one_pow]
  obtain ⟨u₀, hu₀F, hu₀2, hu₀1, hu₀m⟩ :=
    CFSG.Walter.J1.A5Sub.exists_inv X.h.iso X.m_mem_F X.m_ne_one hm15
  have hu₀t : u₀ * X.t = X.t * u₀ := X.h.commute_of_mem_F hu₀F
  have hu₀sq : u₀ * u₀ = 1 := by rw [← pow_two]; exact hu₀2
  have hu₀inv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀sq
  have hs2 : s * s = 1 := (orderOf_eq_two_iff.mp hs).1
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htinv : X.t⁻¹ = X.t := X.h.t_inv
  obtain ⟨hp5, hp1⟩ := X.pow_five hs hsm hst
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨p, hp⟩ : ∃ p, p = X.t * s := ⟨_, rfl⟩
  rw [← hp] at hp5 hp1
  obtain ⟨A, -, -, -, hA, hodd, habel, -⟩ := X.exists_A (Or.inl rfl) X.card_zpowers_m
    X.h.orderOf_t X.zpowers_m_le
  have hpm : p * X.m = X.m * p := by
    rw [hp, mul_assoc, hsm, ← mul_assoc, ← X.m_t, mul_assoc]
  have hpo : orderOf p = 5 := orderOf_eq_prime hp5 hp1
  have hpA : p ∈ A := hodd p ((mem_centralizer_zpowers_iff' _ _).mpr hpm) (by rw [hpo]; decide)
  obtain ⟨q, hq⟩ : ∃ q, q = u₀ * p * u₀⁻¹ := ⟨_, rfl⟩
  have hqm : q * X.m = X.m * q := by
    have h1 := conj_commute (g := u₀) hpm
    rw [hu₀m, ← hq] at h1
    calc q * X.m = X.m * (X.m⁻¹ * q) * X.m := by group
      _ = X.m * (q * X.m⁻¹) * X.m := by rw [h1]
      _ = X.m * q := by group
  have hqo : orderOf q = 5 := by rw [hq, orderOf_conj', hpo]
  have hq5 : q ^ 5 = 1 := by rw [← hqo]; exact pow_orderOf_eq_one q
  have hqA : q ∈ A := hodd q ((mem_centralizer_zpowers_iff' _ _).mpr hqm) (by rw [hqo]; decide)
  have hqmem : q ∈ Subgroup.zpowers p := mem_zpowers_of_comm habel (p := 5) (by norm_num)
    (by rw [hA]; norm_num) hqA hpA hq5 hp5 hp1
  obtain ⟨k, hk5, hqk⟩ := exists_pow_of_mem_zpowers (n := 5) (by norm_num) hp5 hqmem
  have hback : u₀ * q * u₀⁻¹ = p := by
    rw [hq, hu₀inv]
    calc u₀ * (u₀ * p * u₀) * u₀ = (u₀ * u₀) * p * (u₀ * u₀) := by group
      _ = p := by rw [hu₀sq, one_mul, mul_one]
  have hkk : p ^ (k * k) = p ^ 1 := by
    calc p ^ (k * k) = (p ^ k) ^ k := pow_mul p k k
      _ = q ^ k := by rw [hqk]
      _ = u₀ * p ^ k * u₀⁻¹ := by rw [hq, conj_pow]
      _ = u₀ * q * u₀⁻¹ := by rw [hqk]
      _ = p ^ 1 := by rw [pow_one, hback]
  have hmod := pow_eq_pow_iff_modEq.mp hkk
  rw [hpo] at hmod
  interval_cases k
  · exact absurd hmod (by decide)
  ·
    refine ⟨u₀, orderOf_eq_two_iff.mpr ⟨hu₀sq, hu₀1⟩, hu₀t, ?_, hu₀m⟩
    have hup : u₀ * p = p * u₀ := by
      rw [pow_one] at hqk
      rw [← mul_inv_eq_iff_eq_mul, ← hq, hqk]
    have hs' : s = X.t * p := by rw [hp, ← mul_assoc, X.t_mul_t, one_mul]
    rw [hs', ← mul_assoc, hu₀t, mul_assoc, hup, ← mul_assoc]
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  ·
    have hp4 : p ^ 4 = p⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hp5]
    have hup : u₀ * p * u₀⁻¹ = p⁻¹ := by rw [← hq, hqk, hp4]
    refine ⟨u₀ * X.t, ?_, ?_, ?_, ?_⟩
    · refine orderOf_eq_two_iff.mpr ⟨?_, ?_⟩
      · calc u₀ * X.t * (u₀ * X.t) = u₀ * (X.t * u₀) * X.t := by group
          _ = 1 := by rw [← hu₀t, ← mul_assoc, hu₀sq, one_mul, X.t_mul_t]
      · intro h1
        apply X.t_not_mem_F
        have : X.t = u₀⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← hu₀t]; exact h1
        rw [this]
        exact X.F.inv_mem hu₀F
    · rw [← mul_assoc X.t, ← hu₀t]
    · have htp : X.t * p * X.t⁻¹ = p⁻¹ := by
        rw [hp, htinv, mul_inv_rev, hsinv, htinv, ← mul_assoc, X.t_mul_t, one_mul]
      have hconj : (u₀ * X.t) * p * (u₀ * X.t)⁻¹ = p := by
        calc (u₀ * X.t) * p * (u₀ * X.t)⁻¹ = u₀ * (X.t * p * X.t⁻¹) * u₀⁻¹ := by group
          _ = (u₀ * p * u₀⁻¹)⁻¹ := by rw [htp]; group
          _ = p := by rw [hup, inv_inv]
      have hcp : (u₀ * X.t) * p = p * (u₀ * X.t) := mul_inv_eq_iff_eq_mul.mp hconj
      have hs' : s = X.t * p := by rw [hp, ← mul_assoc, X.t_mul_t, one_mul]
      have hut : (u₀ * X.t) * X.t = X.t * (u₀ * X.t) := by rw [← mul_assoc X.t, ← hu₀t]
      rw [hs', ← mul_assoc, hut, mul_assoc, hcp, ← mul_assoc]
    · have htmt : X.t * X.m * X.t⁻¹ = X.m := by
        rw [← X.m_t, mul_inv_cancel_right]
      calc u₀ * X.t * X.m * (u₀ * X.t)⁻¹ = u₀ * (X.t * X.m * X.t⁻¹) * u₀⁻¹ := by group
        _ = X.m⁻¹ := by rw [htmt, hu₀m]

end Setup

end CFSG.Walter.J1Recog
