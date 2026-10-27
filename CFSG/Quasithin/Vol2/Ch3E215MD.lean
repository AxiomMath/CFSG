module

public import CFSG.Quasithin.Vol2.Ch3E215MB
public import CFSG.Quasithin.Vol2.Ch3E213MFam

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 E2 CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem exists_two_pow_le_of_orderOf (h : E2.Pair X T M V g) (hchar : CharTwo X) {c : G}
    (hcX : c ∈ X) {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hc : orderOf c = ℓ ^ (a + 1)) :
    ∃ m : ℕ, 0 < m ∧ ℓ ^ (a + 1) ∣ 2 ^ m - 1 ∧
      2 ^ m ≤ ((V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  set Z := V ⊓ conjSub g V with hZ
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_P
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hZP : Z ≤ P := h.inf_conj_le_P
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hP2
  set c' : Subgroup.normalizer (P : Set G) := ⟨c, hXP hcX⟩ with hc'
  have hc'ord : orderOf c' = ℓ ^ (a + 1) := by rw [hc', Subgroup.orderOf_mk, hc]
  have hc0X : c ^ ℓ ^ a ∈ X := X.pow_mem hcX _
  have hcoe : ((c' ^ ℓ ^ a : Subgroup.normalizer (P : Set G)) : G) = c ^ ℓ ^ a := by
    rw [Subgroup.coe_pow]
  have hne : P.normalizerMonoidHom (c' ^ ℓ ^ a) ≠ 1 := by
    intro h1
    have hc0C : c ^ ℓ ^ a ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨p, hp⟩)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe, MulAut.one_apply] at h2
      calc p * c ^ ℓ ^ a = (c ^ ℓ ^ a * p * (c ^ ℓ ^ a)⁻¹) * c ^ ℓ ^ a := by rw [h2]
        _ = c ^ ℓ ^ a * p := by group
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stable hXP hP2 hchar hc0X hc0C
      (fun q hq => h.commutator_mem_P_of_mem_pCoreOf hc0X hq)
    have hord : orderOf (c ^ ℓ ^ a) = ℓ := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (hc ▸ pow_dvd_pow ℓ (Nat.le_succ a)), hc,
        pow_succ, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos _)]
    have hodd : Odd (orderOf (c ^ ℓ ^ a)) := by
      rw [hord]
      exact hℓ.odd_of_ne_two hℓ2
    have h1' := eq_one_of_two_pow_of_odd hn hodd
    rw [h1', orderOf_one] at hord
    exact hℓ.one_lt.ne hord
  have hfixZ : ∀ z ∈ Z.subgroupOf P, P.normalizerMonoidHom (c' ^ ℓ ^ a) z = z := by
    intro z hz
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe]
    have hzc := h.mem_center (Subgroup.mem_subgroupOf.mp hz) hc0X
    rw [← hzc]
    group
  obtain ⟨m, hm0, hmZ, hmdvd⟩ := Ch3E213M.exists_two_pow_of_orderOf P.normalizerMonoidHom hd hℓ
    hℓ2 hc'ord hne (Z.subgroupOf P) hfixZ
  have hZcard : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hPZ : Z.relIndex P * Nat.card Z = Nat.card P := by
    have h1 := Subgroup.relIndex_mul_card Z P
    rwa [inf_eq_left.2 hZP] at h1
  have h2m : 2 ^ m ≤ Z.relIndex P := by
    rw [hZcard, ← hd, ← hPZ] at hmZ
    exact Nat.le_of_mul_le_mul_right hmZ Nat.card_pos
  exact ⟨m, hm0, hmdvd, h2m.trans (Ch3E213M.relIndex_P_eq h).le⟩

theorem two_pow_le_of_primitive (h : E2.Pair X T M V g) (hchar : CharTwo X) {r k : ℕ}
    (hk : 0 < k) (hr : IsPrimitivePrimeDivisor r k) (hrX : r ∣ Nat.card X) :
    2 ^ k ≤ ((V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrX
  obtain ⟨m, hm, hdvd, hle⟩ := exists_two_pow_le_of_orderOf h hchar x.2 (a := 0) hr.prime
    (hr.ne_two hk) (by rw [pow_one, Subgroup.orderOf_coe, hx])
  rw [zero_add, pow_one] at hdvd
  exact (Nat.pow_le_pow_right two_pos
    (Nat.le_of_dvd hm ((hr.dvd_sub_one_iff hk m).1 hdvd))).trans hle

theorem e215DataOf_of_psl2 (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 2 ≤ n)
    (hcard : (kerIn M X).relIndex X = 2 ^ n * ((2 ^ n) ^ 2 - 1))
    (h9 : n = 3 → ∃ c ∈ X, orderOf c = 9)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂)
    (hidx : M.relIndex X = 2 ^ n + 1) : E215DataOf X M V g := by
  have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hVle := Ch3E213M.relIndex_le_two_pow h
    (by rw [hq]; exact Ch3E213M.odd_two_pow_sub_one (by omega)) hcard
  have hqb : 2 ^ n ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
    by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨c, hcX, hc⟩ := h9 rfl
      obtain ⟨m, hm, hdvd, hle⟩ := exists_two_pow_le_of_orderOf h hchar hcX (ℓ := 3) (a := 1)
        Nat.prime_three (by norm_num) (by rw [hc]; norm_num)
      have h6 : 6 ∣ m := Ch3E213M.six_dvd_of_nine_dvd_two_pow_sub_one (by simpa using hdvd)
      refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
      calc (2 ^ 3) ^ 2 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm h6)
        _ ≤ _ := hle
    · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
      have h1 : r ∣ (2 ^ n) ^ 2 - 1 := by
        rw [hq]
        exact hr.dvd
      have hrX : r ∣ Nat.card X :=
        (h1.trans (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
      refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
      rw [hq]
      exact two_pow_le_of_primitive h hchar (by omega) hr hrX
  rcases (hVle.trans hqb).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact e215DataOf_of_bruhat h hBru (by rw [hidx]; omega)

theorem e215DataOf_of_sz (h : E2.Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 3 ≤ n)
    (hcard : (kerIn M X).relIndex X = (2 ^ n) ^ 2 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)))
    (hV : (kerIn M X ⊓ V).relIndex V ≤ 2 ^ n) : E215DataOf X M V g := by
  left
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  have hrX : r ∣ Nat.card X :=
    (((Ch3E213M.primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
      (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
  have h1 := two_pow_le_of_primitive h hchar (k := 4 * n) (by omega) hr hrX
  have e : ((2 ^ n) ^ 2) ^ 2 = 2 ^ (4 * n) := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  have h2 : (2 ^ n) ^ 2 ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 (e ▸ h1)
  have h3 : 2 ^ n < (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  omega

end CFSG.Quasithin.Ch3E215M
