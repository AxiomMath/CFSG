module

public import CFSG.Quasithin.Background.E2PairMore

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6 E2

theorem card_dvd_card_sub_of_fixed_subset {K β : Type*} [Group K] [Finite K] [MulAction K β]
    [Finite β] {C : Set β} (hC : ∀ k : K, ∀ x ∈ C, k • x ∈ C)
    (hfix : ∀ k : K, k ≠ 1 → ∀ x : β, k • x = x → x ∈ C) :
    Nat.card K ∣ Nat.card β - Nat.card C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype β := Fintype.ofFinite β
  let S : SubMulAction K β :=
    { carrier := Cᶜ
      smul_mem' := fun k x hx hk => hx (by
        have := hC k⁻¹ _ hk
        simpa using this) }
  have hfree : ∀ k : K, k ≠ 1 → ∀ x : S, k • x ≠ x := by
    intro k hk x hx
    have hx' : k • (x : β) = x := by
      have := congrArg Subtype.val hx
      simpa using this
    exact x.2 (hfix k hk x hx')
  have : Fintype S := Fintype.ofFinite S
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K S
  have hsum : (∑ k : K, Fintype.card (MulAction.fixedBy S k)) = Fintype.card S := by
    rw [Finset.sum_eq_single (1 : K)]
    · simp
    · intro k _ hk
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨x, hx⟩ => hfree k hk x hx⟩
    · simp
  rw [hsum] at h
  have hS : Nat.card S = Nat.card β - Nat.card C := by
    have h1 : Nat.card S = Nat.card (Cᶜ : Set β) := rfl
    rw [h1, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_compl]
  rw [← hS, Nat.card_eq_fintype_card (α := S), Nat.card_eq_fintype_card (α := K)]
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel K S)), by rw [h, mul_comm]⟩

theorem pow_mem_zpowers_of_ne_one {J : Type*} [Group J] {c : J} {ℓ a : ℕ} (hℓ : ℓ.Prime)
    (hc : orderOf c = ℓ ^ (a + 1)) {k : J} (hk : k ∈ Subgroup.zpowers c) (hk1 : k ≠ 1) :
    c ^ ℓ ^ a ∈ Subgroup.zpowers k := by
  have hkdvd : orderOf k ∣ ℓ ^ (a + 1) := hc ▸ orderOf_dvd_of_mem_zpowers hk
  obtain ⟨j, -, hkj⟩ := (Nat.dvd_prime_pow hℓ).1 hkdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hkj
    exact hk1 hkj
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hyord : orderOf (k ^ ℓ ^ j') = ℓ := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (hkj ▸ pow_dvd_pow ℓ (Nat.le_succ j')),
      hkj, pow_succ, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos _)]
  have hc0ord : orderOf (c ^ ℓ ^ a) = ℓ := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (hc ▸ pow_dvd_pow ℓ (Nat.le_succ a)), hc,
      pow_succ, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos _)]
  have hyc : k ^ ℓ ^ j' ∈ Subgroup.zpowers (c ^ ℓ ^ a) := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.zpowers c).pow_mem hk (ℓ ^ j'))
    have h1 : (c ^ i) ^ ℓ = 1 := by rw [hi, ← orderOf_dvd_iff_pow_eq_one, hyord]
    rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hc] at h1
    have h2 : ((ℓ ^ a : ℕ) : ℤ) ∣ i := by
      have h3 : ((ℓ ^ a : ℕ) : ℤ) * ℓ ∣ i * ℓ := by
        rw [← Nat.cast_mul, ← pow_succ]
        exact h1
      exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hℓ.ne_zero) h3
    obtain ⟨t, ht⟩ := h2
    refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
    rw [← hi, ht, zpow_mul, zpow_natCast]
  have : Finite (Subgroup.zpowers (c ^ ℓ ^ a)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hc0ord]; exact hℓ.ne_zero)
  have heq : Subgroup.zpowers (k ^ ℓ ^ j') = Subgroup.zpowers (c ^ ℓ ^ a) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hyord, hc0ord])
  have hmem : c ^ ℓ ^ a ∈ Subgroup.zpowers (k ^ ℓ ^ j') := heq ▸ Subgroup.mem_zpowers _
  exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers k).pow_mem (Subgroup.mem_zpowers k) _) hmem

theorem exists_two_pow_of_orderOf {J N : Type*} [Group J] [Group N] [Finite N]
    (ρ : J →* MulAut N) {d ℓ a : ℕ} (hN : Nat.card N = 2 ^ d) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {c : J} (hc : orderOf c = ℓ ^ (a + 1)) (hne : ρ (c ^ ℓ ^ a) ≠ 1) (Z : Subgroup N)
    (hZ : ∀ z ∈ Z, ρ (c ^ ℓ ^ a) z = z) :
    ∃ m : ℕ, 0 < m ∧ 2 ^ m * Nat.card Z ≤ 2 ^ d ∧ ℓ ^ (a + 1) ∣ 2 ^ m - 1 := by
  set c₀ := c ^ ℓ ^ a with hc₀
  let F : Subgroup N :=
    { carrier := {x | ρ c₀ x = x}
      mul_mem' := fun {x y} hx hy => by
        have hx' : ρ c₀ x = x := hx
        have hy' : ρ c₀ y = y := hy
        show ρ c₀ (x * y) = x * y
        rw [map_mul, hx', hy']
      one_mem' := by
        show ρ c₀ 1 = 1
        exact map_one _
      inv_mem' := fun {x} hx => by
        have hx' : ρ c₀ x = x := hx
        show ρ c₀ x⁻¹ = x⁻¹
        rw [map_inv, hx'] }
  obtain ⟨e, hed, hFe⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (hN ▸ Subgroup.card_subgroup_dvd_card F)
  have hlt : e < d := by
    refine lt_of_le_of_ne hed fun hde => hne ?_
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hFe, hN, hde])
    ext x
    exact (htop ▸ Subgroup.mem_top x : x ∈ F)
  have hZe : Nat.card Z ≤ 2 ^ e :=
    hFe ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le fun z hz => hZ z hz)
  let K : Subgroup J := Subgroup.zpowers c
  have hK : Nat.card K = ℓ ^ (a + 1) := by rw [Nat.card_zpowers, hc]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  let _ : MulAction K N := MulAction.compHom N (ρ.comp K.subtype)
  have hsmul : ∀ (k : K) (x : N), k • x = ρ (k : J) x := fun k x => rfl
  have hcomm : ∀ k : K, Commute (k : J) c₀ := by
    intro k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp k.2
    rw [← hj]
    exact Commute.zpow_left (Commute.pow_right (Commute.refl c) _) j
  have hdvd := card_dvd_card_sub_of_fixed_subset (K := K) (β := N) (C := (F : Set N))
    (fun k x hx => by
      have hx' : ρ c₀ x = x := hx
      show ρ c₀ (k • x) = k • x
      rw [hsmul, ← MulAut.mul_apply, ← map_mul, (hcomm k).symm.eq, map_mul, MulAut.mul_apply,
        hx'])
    (fun k hk x hx => by
      have hk' : (k : J) ≠ 1 := fun h => hk (Subtype.ext h)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (pow_mem_zpowers_of_ne_one hℓ hc k.2 hk')
      have hst : ρ (k : J) ∈ MulAction.stabilizer (MulAut N) x := hx
      have h1 := (MulAction.stabilizer (MulAut N) x).zpow_mem hst j
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow, hj] at h1
      exact h1)
  rw [hK, hN] at hdvd
  have hCcard : Nat.card (F : Set N) = 2 ^ e := hFe
  rw [hCcard] at hdvd
  have hfac : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [hfac] at hdvd
  have hcop : Nat.Coprime (ℓ ^ (a + 1)) (2 ^ e) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓ Nat.prime_two).2 hℓ2)
  refine ⟨d - e, by omega, ?_, hcop.dvd_of_dvd_mul_left hdvd⟩
  calc 2 ^ (d - e) * Nat.card Z ≤ 2 ^ (d - e) * 2 ^ e := Nat.mul_le_mul_left _ hZe
    _ = 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hlt.le]

theorem six_dvd_of_nine_dvd_two_pow_sub_one {m : ℕ} (h : 9 ∣ 2 ^ m - 1) : 6 ∣ m := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ m % 9 = 1 := by omega
  have h3 : 2 ^ m % 9 = 2 ^ (m % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod m 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h3] at h2
  have h4 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h5 : m % 6 = 0 := by
    interval_cases hr : m % 6 <;> simp_all
  omega

section Pair

variable {G : Type*} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem isTwo_of_centralizes (h : Pair X T M V g) (hchar : CharTwo X) {d : G} (hdX : d ∈ X)
    (hd : ∀ p ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V),
      d * p * d⁻¹ * p⁻¹ ∈ V ⊓ conjSub g V) :
    ∃ n : ℕ, d ^ 2 ^ n = 1 := by
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_P
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hd2X : d ^ 2 ∈ X := X.pow_mem hdX 2
  have hd2C : d ^ 2 ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    set z := d * p * d⁻¹ * p⁻¹ with hz
    have hzZ : z ∈ V ⊓ conjSub g V := hd p hp
    have hzd : z * d = d * z := h.mem_center hzZ hdX
    have hz2 : z * z = 1 := by
      have := h.elem.2 z hzZ.1
      rwa [pow_two] at this
    have e1 : d * p * d⁻¹ = z * p := by rw [hz]; group
    have e2 : d ^ 2 * p * (d ^ 2)⁻¹ = p := by
      calc d ^ 2 * p * (d ^ 2)⁻¹ = d * (d * p * d⁻¹) * d⁻¹ := by rw [pow_two]; group
        _ = d * (z * p) * d⁻¹ := by rw [e1]
        _ = (d * z * d⁻¹) * (d * p * d⁻¹) := by group
        _ = z * (z * p) := by rw [e1, ← hzd]; group
        _ = p := by rw [← mul_assoc, hz2, one_mul]
    calc p * d ^ 2 = (d ^ 2 * p * (d ^ 2)⁻¹) * d ^ 2 := by rw [e2]
      _ = d ^ 2 * p := by group
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stable hXP hP2 hchar hd2X hd2C
    (fun q hq => h.commutator_mem_P_of_mem_pCoreOf hd2X hq)
  exact ⟨n + 1, by rw [pow_succ', pow_mul, hn]⟩

theorem relIndex_P_eq (h : Pair X T M V g) :
    (V ⊓ conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) =
      ((V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V)) ^ 2 := by
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  have hZB : Z ≤ B := h.inf_conj_le_kerIn_inf
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := le_sup_right.trans h.P_le_normalizer_B
  have h1 : B.relIndex (B ⊔ A) = Z.relIndex A := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hAB
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
    have e : B.relIndex (A ⊔ B) = B.relIndex A :=
      Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv.symm
    rw [sup_comm, e, ← Subgroup.inf_relIndex_right, h.B_inf_A]
  have h2 : Z.relIndex A = Z.relIndex B := by
    have hZg : conjSub g Z = Z := h.conjSub_inf_conj h.mem
    rw [hA]
    conv_lhs => rw [← hZg]
    show (Z.map (MulAut.conj g).toMonoidHom).relIndex (B.map (MulAut.conj g).toMonoidHom) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ fun x y hxy => (MulAut.conj g).injective hxy
  rw [← Subgroup.relIndex_mul_relIndex Z B (B ⊔ A) hZB le_sup_left, h1, h2, sq]

theorem relIndex_le_of_orderOf (h : Pair X T M V g) (hchar : CharTwo X) {c : G} (hcX : c ∈ X)
    {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hc : orderOf c = ℓ ^ (a + 1))
    (hV : ∀ m : ℕ, 0 < m → ℓ ^ (a + 1) ∣ 2 ^ m - 1 →
      ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ 2 ^ m) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
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
  obtain ⟨m, hm0, hmZ, hmdvd⟩ :=
    exists_two_pow_of_orderOf P.normalizerMonoidHom hd hℓ hℓ2 hc'ord hne (Z.subgroupOf P) hfixZ
  have hZcard : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hPZ : Z.relIndex P * Nat.card Z = Nat.card P := by
    have h1 := Subgroup.relIndex_mul_card Z P
    rwa [inf_eq_left.2 hZP] at h1
  have h2m : 2 ^ m ≤ Z.relIndex P := by
    rw [hZcard, ← hd, ← hPZ] at hmZ
    exact Nat.le_of_mul_le_mul_right hmZ Nat.card_pos
  have hsq := (hV m hm0 hmdvd).trans (h2m.trans (relIndex_P_eq h).le)
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 hsq

end Pair

end CFSG.Quasithin.Ch3E213M
